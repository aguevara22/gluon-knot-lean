import SM.LinkInterfaces

/-! Ported 2026-09-13 from work/drafts/LocalPolynomial_statement.lean (pod executor; checked with `lake env lean`, no sorry). -/

/-! The local campaign polynomial `P` of lp:core (reference/SM/sm-3-statesum.tex:1041-1063, frame SM15):
"the same source construction has an evaluation `P_D ∈ R`", namely the Gaussian evaluation
`P_D^G = φ(F_D)` (eq. lp:gaussian, `φ(l) = i a`, `φ(m) = −i z`) of the source value `F_D` of lp:lm,
which lp:core proves to lie in the image of `R ⊂ R_G` ("integral descent"). Lean rendering: `P D` is the
real part (`reMap`, the coefficientwise `GaussianInt.re`) of `phi (T.toTG (lmF D))`; lp:core's bundle
records `R.toRG (P D) = phi (T.toTG (lmF D))`, i.e. that the imaginary part vanishes, so `P D` is exactly
the element of `R` whose image in `R_G` is `φ(F_D)`. Notation: namespace `SM.Link` — `R`, `T`, `RG`, `TG`,
`R.toRG`, `T.toTG`, `phi : TG →ₐ[GaussianInt] RG`, `reMap : Laurent₂ GaussianInt →+ Laurent₂ ℤ`
(SM/LinkLaurentRing.lean); `lmF` the source function fixed by lp:lm (SM/LinkInterfaces.lean). -/

namespace SM

open SM.Link

/-- The local campaign polynomial `P_D ∈ R` (lp:core, eq. lp:gaussian): the element of `R` whose
image in `R_G` is the Gaussian evaluation `φ(F_D)` of the source value — read off as the real part of
`φ(F_D)` (the imaginary part vanishes by lp:core's integral descent). -/
noncomputable def P (D : Diagram) : R := reMap (phi (T.toTG (lmF D)))

/-- Sanity: on a diagram with source value `1`, `P` is `1`. -/
theorem P_eq_one_of_lmF_eq_one {D : Diagram} (h : lmF D = 1) : P D = 1 := by
  unfold P
  rw [h, map_one, map_one]
  simpa using reMap_toRG (1 : R)

end SM
