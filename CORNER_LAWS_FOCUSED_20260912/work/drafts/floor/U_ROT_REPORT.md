# U-ROT report — unit ROT (prefix `urot_`), 2026-09-15

File: `work/drafts/floor/U_ROT.lean` (copy of `Statements_FINAL.lean`; statements frozen, byte-identical
apart from the two hunks below). Check: `cd work/lean && lake env lean ../drafts/floor/U_ROT.lean` —
**0 errors**, 22 warnings, all `declaration uses 'sorry'` from the other units' leaves (none names a
`urot_` declaration). `grep -c sorry`: 25 before → 24 after (the one removed is the leaf's body; the
remaining 24 = 22 other leaves + 2 mentions inside docstrings).

`diff Statements_FINAL.lean U_ROT.lean`: `595a596,737` (the helper block, inserted right after `def downDir`,
before the leaf's docstring, same section 8.5) and `603c745,749` (the `sorry` line → the 5-line proof body).
No definition, structure, statement, name or docstring was changed.

`#print axioms` (checked on the scratch copy, same code): `urot_exists_rotated` and `urot_recordCarried`
depend on `[propext, Classical.choice, Quot.sound]` only — no `SM.lp_lm`, no `SM.lit_homfly`.

## Leaves

| leaf | status |
|---|---|
| `urot_exists_rotated` | **PROVED** |

No leaf of this unit is left; nothing in the statement is false or under-hypothesised — the leaf is
exactly as strong as needed (`hu : euclideanLength u = 1` is used once, to write `u = (cos α, sin α)`).

## Proof route as executed (PLAN_FINAL §3 (C) step 5)

`α := Complex.arg (planeComplex u)`, `φ := −(π/2) − α`. Then `rotPlane φ u = downDir` because
`u = (cos α, sin α)` (accepted `CornerRounding.G1_smul_dirOf_arg u` with `hu`), `rotPlane φ (cos α, sin α)
= (cos (α+φ), sin (α+φ))` and `α + φ = −π/2`. `G := urot_loop φ F` with `γ := rotPlane φ ∘ F.γ`; the
record is `urot_recordCarried φ c` with the SAME `τ` (`one`, `τ_mem`, `τ_inj`, `order` verbatim;
`twin_eval` by `congrArg`; `doubles` through injectivity of `rotPlane φ`; `transverse`/`sign_eq` through
`det (rotPlane φ a) (rotPlane φ b) = det a b`). Tangent clause: `deriv G.γ t = rotPlane φ (deriv F.γ t)`,
`normalize (rotPlane φ w) = rotPlane φ (normalize w)` (length invariance + homogeneity), then
`rotPlane φ (normalize w) = rotPlane φ u ↔ normalize w = u` by injectivity (`Function.Injective.eq_iff`).

## Helpers added (all in section 8.5, between `def downDir` and the leaf; 142 lines)

Algebra of `rotPlane`:
- `urot_rotPlane_smul (φ r p) : rotPlane φ (r • p) = r • rotPlane φ p`
- `urot_rotPlane_add (φ p q) : rotPlane φ (p + q) = rotPlane φ p + rotPlane φ q`
- `urot_rotPlane_neg_rotPlane (φ p) : rotPlane (-φ) (rotPlane φ p) = p`
- `urot_rotPlane_injective (φ) : Function.Injective (rotPlane φ)`
- `urot_det_rotPlane (φ a b) : det (rotPlane φ a) (rotPlane φ b) = det a b`
- `urot_euclideanLength_rotPlane (φ p) : euclideanLength (rotPlane φ p) = euclideanLength p`
- `urot_normalize_rotPlane (φ p) : SM.normalize (rotPlane φ p) = rotPlane φ (SM.normalize p)`
- `urot_rotPlane_cos_sin (φ α) : rotPlane φ (cos α, sin α) = (cos (α + φ), sin (α + φ))`
- `urot_unit_eq_cos_sin (u) (hu) : u = (cos (arg (planeComplex u)), sin (arg (planeComplex u)))`
- `urot_rotPlane_unit_eq_downDir (u) (hu) : rotPlane (-(π/2) - arg (planeComplex u)) u = downDir`

Analysis (the rotation as a continuous linear map, so `ContDiff` and `deriv` commute with it for free):
- `def urot_rotLin (φ) : Plane →ₗ[ℝ] Plane`, `def urot_rotCLM (φ) : Plane →L[ℝ] Plane`
  (`LinearMap.toContinuousLinearMap`, finite-dimensional domain), `urot_rotCLM_apply`, `urot_rotCLM_coe` (both `rfl`)
- `urot_smooth (φ) (F : SmoothLoop) : ContDiff ℝ ∞ (rotPlane φ ∘ F.γ)`
- `urot_periodic (φ) (F : SmoothLoop) : Function.Periodic (rotPlane φ ∘ F.γ) 1`
- `urot_hasDerivAt (φ F t) : HasDerivAt (rotPlane φ ∘ F.γ) (rotPlane φ (deriv F.γ t)) t`, `urot_deriv`

Constructions:
- `def urot_loop (φ) (F : SmoothRegularLoop) : SmoothRegularLoop` (`γ := rotPlane φ ∘ F.γ`), `urot_loop_γ` (`rfl`),
  `urot_loop_deriv (φ F t) : deriv (urot_loop φ F).γ t = rotPlane φ (deriv F.γ t)`
- `def urot_recordCarried (φ) (c : RecordCarried F X) : RecordCarried (urot_loop φ F) X` (same `τ`)

These are reusable by U-LIFT-3 / U-C if they need the rotated loop's velocity or the transported record's
`τ` explicitly: the witness produced by the leaf is definitionally `urot_loop φ F` with record
`urot_recordCarried φ c`, and `(urot_recordCarried φ c).τ = c.τ` by `rfl` (no lemma stated, to keep the
helper block small; add one with prefix `urot_` if a consumer wants it).

## Mathlib pitfalls met (v4.34.0-rc2 pin)

- `conv_lhs => rw [h]` with `h : u = (cos (arg u), sin (arg u))` rewrites EVERY `u` on the LHS, including the
  one inside the angle `−π/2 − arg u`, producing a non-terminating shape. Fix used: `generalize Complex.arg
  (planeComplex u) = α at h ⊢` first, then `rw [h]`.
- After `rw [urot_rotCLM_coe] at h` the applied form `(urot_rotCLM φ) v` is ALREADY rewritten to `rotPlane φ v`
  (the coercion rewrite hits the application); a further `rw [urot_rotCLM_apply]` fails with "did not find
  an occurrence". Use only the `coe` rewrite.
- `LinearMap.toContinuousLinearMap` on `ℝ × ℝ` works out of the box (`FiniteDimensional` instance found);
  `⇑(LinearMap.toContinuousLinearMap f) = ⇑f` is `rfl` here, so `urot_rotCLM_coe` needs no simp lemma.
- Trig identities: `linear_combination (…) * Real.cos_sq_add_sin_sq φ` closes all the `cos²+sin²` goals
  (`det`, length, inverse rotation) without `nlinarith`.
- `Function.Periodic.comp` is `protected`: call it as `F.periodic.comp (rotPlane φ)`.

## For the assembler / executor

- Nothing outside section 8.5 was touched; the block can be concatenated verbatim. No name clashes with
  work/lean/SM (`rotationMap` avoided as PLAN_FINAL §2.4 requires; all new names start `urot_`).
- FR-FL-C6 stands as written: the leaf rotates the smooth curve only; `X` and `τ` are unchanged.
- The leaf's `φ` is `−(π/2) − Complex.arg (planeComplex u)`; if a downstream unit prefers an explicit
  witness, `urot_loop`/`urot_recordCarried` are the ones the existential is built from.
