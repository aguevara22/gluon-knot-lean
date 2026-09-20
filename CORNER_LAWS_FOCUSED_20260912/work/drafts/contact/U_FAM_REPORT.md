# U_FAM_REPORT — unit FAM (U6 + U6a), leaves `u_regular`, `u_family`

Prover, 2026-09-15.  File: `work/drafts/contact/U_FAM.lean` (copy of `Skeleton_FINAL.lean`; only the two
`sorry` bodies of this unit replaced, helpers prefixed `ufm_` inserted between `u_regular` and `u_family`).

Compile: `cd work/lean && lake env lean ../drafts/contact/U_FAM.lean` → 0 errors, 9 warnings
"declaration uses `sorry`" (the 9 leaves of the other units, lines 551-567).  `grep -c sorry`: 12 before
(11 leaves + 1 docstring mention) → 10 after (9 leaves + the docstring).
`diff Skeleton_FINAL.lean U_FAM.lean`: the only removed lines are the two `sorry`s; every other line is an
addition inside §5.4.  No definition, structure, axiom, statement, name or docstring touched.

Axiom footprint (checked with `#print axioms` on a scratch copy of the same declarations):
`SM.u_regular` and `SM.u_family` depend on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`,
no `SM.src_contact`, no literature axiom.  `u_family` uses `u_regular` (same unit), nothing from other units.

## Leaves proved (2 / 2)

| leaf | content |
|---|---|
| `u_regular : U_regular` | `K.spatial.RegularGenericProjection` field by field: `regular` = `K.immersion`; `doubles_finite` = image of `K.doubles_finite` under `q ↦ ((0 : Fin 1), q.1)` (an occurrence `(i,t)` with partner `(j,t')` gives the pair `(t,t')` of `K`'s set, `t ≠ t'` because `Fin 1` is a subsingleton); `transverse`, `no_triple` = `K.transverse`, `K.no_triple` after `¬SameParam (i,s) (j,t) → ¬SameT s t` (again `Fin 1`); `heights_distinct` = `K.y_ne_of_isDouble`.  No helper needed (≈ 20 lines). |
| `u_family : U_family` | the family of display fd:contact-ambient-composition, `ufm_fam Ψ Φ L t s := toSpace (Ψ (η t) (Φ (1 − η t) (L (2π s))))`, `η = Real.smoothTransition` (Mathlib: `C^∞`, `= 0` on `t ≤ 0`, `= 1` on `t ≥ 1`, values in `[0,1]`), packaged as a `SpatialFamily 1` by `ufm_familyOfSlices`.  `Fam.G 0 = pkg.sp` by `ufm_spatialLink_ext` + `pkg.sp_T` (`η 0 = 0`, `Ψ 0 = id`); `Fam.G 1 = K.spatial` (`η 1 = 1`, `Φ 0 = id`, `Ψ 1 ∘ L = K.circle`, `2πs/(2π) = s`, `toSpace ∘ toE3 = id`); then `RegularGenericProjection` and the `HeightMarking` transport are `rw [h1]` + `u_regular K` / the hypothesis. |

## Helpers added (all before `u_family`, prefix `ufm_`; two are `def`s, flagged)

| name | statement | note |
|---|---|---|
| `ufm_contDiff_toSpace` | `ContDiff ℝ ∞ toSpace` | `contDiff_euclidean.mp contDiff_id` coordinatewise |
| `ufm_clock_mem`, `ufm_clock_mem'` | `η x ∈ Icc 0 1`, `1 − η x ∈ Icc 0 1` | |
| `ufm_contDiff_slice` | `ContDiffOn ℝ ∞ (uncurry Ψ) (Icc 0 1 ×ˢ univ) → t ∈ Icc 0 1 → ContDiff ℝ ∞ (Ψ t)` | `ContDiffOn.comp_contDiff` with `p ↦ (t, p)`; gives smoothness of the boundary slices `Φ 1`, `Ψ 1` too |
| `ufm_deriv_ne_zero_of_leftInverse` | `Differentiable ℝ finv → LeftInverse finv f → DifferentiableAt ℝ (f ∘ γ) θ → deriv γ θ ≠ 0 → deriv (f ∘ γ) θ ≠ 0` (generic normed spaces) | THE regularity device: no injectivity of `fderiv` needed — if `(f∘γ)′ = 0` then `γ′ = (finv ∘ f ∘ γ)′ = D finv (0) = 0` (`HasFDerivAt.comp_hasDerivAt`) |
| `ufm_embeddedCircle_of_comp` | `ContDiff f → ContDiff finv → LeftInverse finv f → IsEmbeddedCircle (f ∘ L) → IsEmbeddedCircle L` (GF's) | recovers `L`'s circle properties from `pkg.F_front.hyp.circle : IsEmbeddedCircle (Φ 1 ∘ L)` and `Φ 1`'s inverse; the statement of `U_family` gives NO direct hypothesis on `L` |
| `ufm_deriv_comp_two_pi` | `deriv (fun s => L (2πs)) s ≠ 0` for an embedded circle | `HasDerivAt.scomp`, `smul_ne_zero` |
| `ufm_spatialLink_ext` | `L.T = L'.T → L = L'` for `SpatialLink c` | `cases; cases; cases h; rfl` (no `@[ext]` on `SpatialLink` in the library) |
| `ufm_ambient_ofGF` | `GenericFront.IsCompactlySupportedAmbientIsotopy Φ → TransverseNeighborhood.IsCompactlySupportedAmbientIsotopy Φ` | eta bridge (same fields), so all family helpers take row 84's structure |
| `def ufm_fam` | the family map above | |
| `ufm_fam_joint_smooth` | `ContDiff ℝ ∞ (fun p : ℝ × ℝ => ufm_fam Ψ Φ L p.1 p.2)` from the two `ContDiffOn (Icc 0 1 ×ˢ univ)` and `ContDiff L` | two `ContDiffOn.comp_contDiff` steps (inner `Φ`, then `Ψ`), membership by the clock lemmas |
| `ufm_fam_periodic` | period 1 in `s` from `Periodic L (2π)` | |
| `ufm_fam_embedded` | `ufm_fam … t s = ufm_fam … t s' → SameT s s'` | `toE3` both sides, `LeftInverse.injective` of `Ψinv`, `Φinv` (from `diffeo` at `η t`, `1 − η t`), `L`'s `injective`, cancel `2π` |
| `ufm_fam_regular` | `deriv (ufm_fam … t) s ≠ 0` | `ufm_deriv_ne_zero_of_leftInverse` with `f = toSpace ∘ Ψ_{η t} ∘ Φ_{1−η t}`, `finv = Φinv ∘ Ψinv ∘ toE3`, `γ = L ∘ (2π·)` |
| `def ufm_familyOfSlices` + `ufm_familyOfSlices_T` | a jointly smooth `F : ℝ → ℝ → Space` with 1-periodic, embedded (`SameT`), regular slices as a `SpatialFamily 1`; `((… ).G t).T = fun _ => F t` (`rfl`) | reusable for any one-component family |

Rule (2) says "helper lemmas"; two of the helpers are `def`s (`ufm_fam`, `ufm_familyOfSlices`) because a
`SpatialFamily` needs a function `ℝ → SpatialLink 1` as data.  Both are prefixed and sit immediately before
`u_family`.  If the assembler prefers theorem-only helpers, `u_family` can inline the structure literal
(the proof uses `obtain ⟨Fam, hFam⟩ : ∃ Fam, ∀ t, (Fam.G t).T = fun _ => ufm_fam Ψ Φ L t` so only the
`rfl` equation of `ufm_familyOfSlices_T` is consumed).

## Notes for the assembler / executor

* Nothing false found; no hypothesis missing.  In particular the statement's lack of a direct hypothesis on
  `L` (only `pkg : LegendrianPackage (Φ 1 ∘ L)` and `Ψ 1 ∘ L = K.circle`) is fine:
  `pkg.F_front.hyp.circle` + the inverse of `Φ 1` recover `IsEmbeddedCircle L` (`ufm_embeddedCircle_of_comp`).
  (`u_circle` / row 84 is NOT used, so this unit does not depend on U0.)
* `Fam.G 1 = K.spatial` holds as an EQUALITY of `SpatialLink 1` (not just `T`-wise), so the endpoint reading is
  transported by `rw`, and `(Fam.G 1).RegularGenericProjection` is literally `u_regular K`.
* The clock is essential twice: `SpatialFamily.joint_smooth` is on all of `ℝ × ℝ` while the isotopies are only
  `ContDiffOn (Icc 0 1 ×ˢ univ)`, and `SpatialFamily.G t` must be a `SpatialLink` for EVERY real `t`
  (`diffeo` is only available on `Icc 0 1`).
* Both leaves are `~200` lines total (plan estimated 750); the regularity trick above is what saved the
  "injective `fderiv` of a diffeomorphism" development.

## Mathlib pitfalls met (pinned Mathlib, Lean v4.34.0-rc2)

* `Real.smoothTransition.zero/.one/.contDiff/.continuous` are `protected` — write the full name; `.contDiff`
  is stated for `n : ℕ∞` and unifies with `∞` (`(⊤ : ℕ∞)` cast) without help.
* `ContDiff.differentiable` needs `1 ≤ ∞`; `(by decide)` works (the accepted `TransverseFront.lean` uses it).
* `rintro rfl` on a goal `(t, t').1 ≠ (t, t').2` fails ("`t'` occurs at `(t, t').1`"); use `intro h` and
  `Prod.ext`.
* `HasFDerivAt.comp_hasDerivAt` takes the point explicitly: `hl.comp_hasDerivAt θ hf`.
* `h3.deriv` for `h3 : HasDerivAt (L ∘ fun s => 2πs) …` is stated on `L ∘ …`; to `rw` in a goal about
  `fun s => L (2πs)` restate it with `have h4 : deriv (fun s => L (2πs)) s = … := h3.deriv` (defeq accepted).
* `ContDiffOn.comp_contDiff` wants the inner map named (`(f := fun p => (…, …))`) when the target function is
  given as a lambda rather than a composition.
