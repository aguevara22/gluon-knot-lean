# GF_U_P6_REPORT.md — unit P6 (concatenation, pushoff annulus, knot type)

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P6.lean` (844 lines; skeleton 625).
Check: `cd work/lean && lake env lean ../drafts/fd/GF_U_P6.lean` → **0 errors**, 22 warnings
`declaration uses sorry` (the 22 leaves of units P0–P5, untouched).  `grep -c sorry`: 27 before
(26 leaves + one mention in the module docstring) → 23 after.  Lines 1–568 of the file are
byte-identical to the skeleton; the diff consists only of inserted `gp6_` helpers and the four
replaced `sorry` bodies (checked with `diff | grep -v '^>'`).

`#print axioms` (on a `/tmp` copy of the file with the commands appended):
- `SM.GenericFront.isContactIsotopy_concat` — `[propext, Classical.choice, Quot.sound]`
- `SM.GenericFront.pushoffAnnulus_map` — `[propext, Classical.choice, Quot.sound]`
- `SM.GenericFront.transverselyIsotopic_contact` — `[propext, Classical.choice, Quot.sound]`
- `SM.GenericFront.IsPushoffAnnulus.circle` — `[propext, Classical.choice, Quot.sound]`
- `SM.fd_generic_front` — still `sorryAx` (through the other units only).

## Leaves proved (4 of 4)

| leaf | name | lines | proof |
|---|---|---|---|
| P6.1 | `isContactIsotopy_concat` | 628–679 | see below |
| P6.2 | `pushoffAnnulus_map` | 732–761 | nine fields, chain rule + conformal factor |
| P6.3 | `transverselyIsotopic_contact` | 776–794 | `F s θ := Φ s (K θ)`, `ρ := id` |
| P6.4 | `IsPushoffAnnulus.circle` | 802–811 | slice of the annulus, `DB(θ,s₀)(1,0) ≠ 0` |

Leaves left: none.  No leaf was false or needed a stronger hypothesis; all four are true exactly
as frozen.

### P6.1 — no gluing lemma was needed
GF_PLAN.md §2 (P6.1) expected the joint smoothness across the join `s = ½` to need a gluing lemma
using the vanishing of all derivatives of `smoothTransition` at `0` and `1`.  It does not: since
`τ := Real.smoothTransition` is *constant* (`= 1`) on `[1, ∞)` and (`= 0`) on `(−∞, 0]`, the left
branch `A(s,p) := Φ (τ(2s)) p` equals `Φ 1 p` for every `s ≥ ½`, and the right branch
`C(s,p) := Ψ (τ(2s−1)) (Φ 1 p)` equals `Ψ 0 (Φ 1 p) = Φ 1 p` for every `s ≤ ½`.  Hence
```
uncurry (concat Φ Ψ) = fun q => A q + C q − Φ 1 q.2        -- `gp6_uncurry_concat_eq`
```
as an exact identity of functions on all of `ℝ × ℝ³`, and the right side is a sum/difference of
three globally `C^∞` maps (`A`, `C` by `ContDiffOn.comp` of `uncurry Φ`/`uncurry Ψ` with maps into
`Icc 0 1 ×ˢ univ`, using `τ ∈ [0,1]`).  The other four clauses split on `s ≤ ½` via the two
branch identities `gp6_concat_of_le` / `gp6_concat_of_not_le` (`concat Φ Ψ s = Φ (τ(2s))`, resp.
`= Ψ (τ(2s−1)) ∘ Φ 1`): `zero` (`τ 0 = 0`, `Φ 0 = id`), `diffeo` (inverse `Φinv ∘ Ψinv`,
`LeftInverse.comp`/`RightInverse.comp`), `support` (`K₁ ∪ K₂`, `IsCompact.union`), `contact`
(`fderiv_comp`, conformal factor `c₂ · c₁`).

## Helpers added (14, all `lemma gp6_…`, each placed immediately before the first leaf using it)

Before P6.1 (lines 569–626):
- `gp6_contDiff_stage` — `IsCompactlySupportedAmbientIsotopy Φ → s ∈ Icc 0 1 → ContDiff ℝ ∞ (Φ s)`
  (slice of the joint smoothness; the same pattern P0.2 uses inline).
- `gp6_contDiff_concat_left`, `gp6_contDiff_concat_right` — the two branches are `C^∞` on `ℝ × ℝ³`.
- `gp6_uncurry_concat_eq` — the identity above (needs only `Ψ 0 = id`).
- `gp6_concat_of_le`, `gp6_concat_of_not_le` — the branch identities as equalities of `ℝ³ → ℝ³`.

Before P6.2 (lines 679–730):
- `gp6_injective_stage` — `Injective (Φ s)` (from the left inverse).
- `gp6_fderiv_stage_injective` — `Injective (fderiv ℝ (Φ s) p)` (`DΨinv ∘ DΦ_s = id` by `fderiv_comp`
  on `Ψinv ∘ Φ s = id`).
- `gp6_hasDerivAt_stage_comp` — `HasDerivAt (fun θ => Φ s (γ θ)) (DΦ_s(γ θ) γ′) θ`.
- `gp6_isPositiveTransverse_stage` — `IsContactIsotopy Φ` carries positive transverse smooth curves
  to positive transverse curves (`α((Φ_s∘K)′) = c · α(K′) > 0`, sm-3:2776-2779).
- `gp6_contDiff_annulus_circle` — `ContDiff ℝ ∞ fun θ => B (θ, s₀)` for `s₀ ∈ Ioo (−ε) b`.
- `gp6_differentiableAt_annulus` — `DifferentiableAt ℝ B (θ, s₀)` (open domain
  `univ ×ˢ Ioo (−ε) b`).

Before P6.3 (line 762): `gp6_isEmbeddedCircle_stage` — a stage of an ambient isotopy carries
embedded circles to embedded circles (no Legendrian hypothesis; this is the circle half of P0.2
without `IsLegendrian`, which P0.2's statement cannot supply for the transverse circle `K`).

Before P6.4 (line 795): `gp6_hasDerivAt_annulus_circle` — `deriv (fun θ => B (θ, s₀)) θ =
fderiv ℝ B (θ, s₀) (1, 0)` as a `HasDerivAt`.

## Mathlib pitfalls met (v4.34.0-rc2 pin)
- `if_pos` / `if_neg` are **deprecated**; use `ite_eq_left h` / `ite_eq_right h` (same shape).
- `simp [concat, hs]` with `hs : s ≤ 1 / 2` **fails**: the default simp set normalises `1 / 2` to
  `2⁻¹` in the goal before `hs` can fire, leaving `2⁻¹ < s → …`.  Use `simp only [concat,
  ite_eq_left hs]` (no arithmetic normalisation).
- `ContDiffOn.differentiableAt` does not exist.  Pattern used:
  `(h.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)` with
  `hopen : IsOpen (univ ×ˢ Ioo (-ε) b) := isOpen_univ.prod isOpen_Ioo`.
- `Real.smoothTransition.contDiff : ∀ {n : ℕ∞}, ContDiff ℝ ↑n smoothTransition`; it unifies with
  `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` without annotation.  `zero_of_nonpos`, `one_of_one_le`, `nonneg`,
  `le_one`, `zero` all exist under `Real.smoothTransition.`.
- `ContDiff.differentiable` wants `n ≠ 0` and `ContDiffOn.differentiableOn` wants `1 ≤ n`; both are
  closed by `(by simp)` for `n = ∞`.
- `Function.LeftInverse.comp : LeftInverse f g → LeftInverse h i → LeftInverse (h ∘ f) (g ∘ i)`,
  so the inverse of `Ψ t ∘ Φ 1` is `hl₂.comp hl₁` with `hl₂` the `Ψ`-inverse (order matters).
- `Injective` of a CLM composition `(g.comp f)`: `intro v w h; exact hf (hg h)` works by `rfl`
  (`ContinuousLinearMap.comp_apply` is definitional); no `coe_comp'` rewrite needed.
- Anonymous-constructor `refine ⟨F, ?_, …, id, ⟨contDiff_id, fun θ => ?_, fun θ => rfl⟩, ?_⟩`
  flattens `∃ F, _ ∧ _ ∧ _ ∧ ∃ ρ, IsCircleReparam ρ ∧ _` fine; `F 1 = T₁ ∘ id` is `rfl`.

## Notes for the assembler / executor
- Nothing outside the four `sorry` bodies and the inserted `gp6_` blocks was changed; all
  definitions, statements, names and docstrings are as in the skeleton.
- The helpers depend only on §1–§2 notions (`IsCompactlySupportedAmbientIsotopy`,
  `IsContactIsotopy`, `IsPushoffAnnulus`, `IsEmbeddedCircle`, `IsPositiveTransverse`) and on
  `concat`; none uses another unit's leaf, row 85 or row 86, so the unit is a leaf of the
  dependency graph and can be merged in any order.
- `gp6_contDiff_stage`, `gp6_fderiv_stage_injective`, `gp6_hasDerivAt_stage_comp` and
  `gp6_isEmbeddedCircle_stage` duplicate work done inline in P0.2 (`GF_U_P0.lean`, `hΦs`, `hinj`,
  `hder`); at assembly one may (optionally) re-prove P0.2 from them, but no clash exists
  (`gp0_` vs `gp6_` prefixes).
- Total added: 219 lines (14 helpers ≈ 150, four leaf bodies ≈ 70), well under the 450 estimate.
