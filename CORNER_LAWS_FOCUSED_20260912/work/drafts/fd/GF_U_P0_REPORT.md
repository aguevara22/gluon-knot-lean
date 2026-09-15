# GF_U_P0_REPORT.md — unit P0 of `GF_Skeleton.lean` (row 87 fd:generic-front)

Date: 2026-09-14.  File: `work/drafts/fd/GF_U_P0.lean` (788 lines; the skeleton was 625).
Check: `cd work/lean && lake env lean ../drafts/fd/GF_U_P0.lean` — **0 errors**, 23 warnings
`declaration uses sorry` (the 23 leaves of units P1–P6, untouched).  `grep -c sorry`: 27 before
(26 leaves + 1 in the module docstring) → 24 after (23 leaves + docstring).
`diff GF_Skeleton.lean GF_U_P0.lean` removes exactly three lines, the three `sorry`s of P0; every
statement, name and docstring is byte-identical to the skeleton.

## Leaves proved (3 of 3)

| leaf | name | axioms |
|---|---|---|
| P0.1 | `isContactIsotopy_hamIsotopy` | `[propext, Classical.choice, Quot.sound]` |
| P0.2 | `contact_preserves_legendrian` | `[propext, Classical.choice, Quot.sound]` |
| P0.3 | `fderiv_composeFlows_zero` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` in any of the three.  `SM.fd_generic_front` still depends on `sorryAx` only through
the other units' leaves.  No leaf was false or needed a stronger hypothesis.

## Leaves left

None in P0.

## Helpers added (all `gp0_`, placed immediately before the leaf that uses them)

Before P0.1 (`isContactIsotopy_hamIsotopy`):
- `gp0_alpha_eq (p v) : alpha p v = ContactMotions.alpha p v := rfl` — the two `alpha`s
  (`SM.GenericFront.alpha`, `SM.ContactMotions.alpha`) are distinct constants with the same body;
  `rw` needs this bridge to use `fd_contact_motions.contact`.
- `gp0_hamFlow_fixed (h : ContactMotionsHyp H) (hp : p ∉ tsupport (hamVF H)) (s) : hamFlow H s p = p`
  — ODE uniqueness against the constant curve (same proof as `globalFlow_fixed_of_notMem` in
  `TN_Skeleton.lean`, via `ContactMotions.ODE_unique_global` and `h.exists_lipschitzWith`).
- `gp0_composeFlows_fixed (n Hs b) (hp : ∀ i s, hamFlow (Hs i) s p = p) : composeFlows n Hs b p = p`
  — induction on `n`.
- `gp0_contDiff_composeFlows (n Hs hHs b) : ContDiff ℝ ∞ (composeFlows n Hs b)` — slice of
  `fd_contact_motions.compositions_smooth`.
- `gp0_composeFlows_inv (n Hs hHs b) : ∃ Ψ, ContDiff ℝ ∞ Ψ ∧ LeftInverse Ψ (composeFlows n Hs b) ∧
  RightInverse Ψ (composeFlows n Hs b)` — induction; `Ψ = Ψ' ∘ hamFlow (Hs 0) (−b 0)` with
  `fd_contact_motions.diffeo` for the single flow.  (An existence statement, so no new `def`.)
- `gp0_composeFlows_contact (n Hs hHs b p) : ∃ c > 0, ∀ v, alpha (composeFlows n Hs b p)
  (fderiv ℝ (composeFlows n Hs b) p v) = c * alpha p v` — induction, chain rule `fderiv_comp`,
  `c = confFactor (Hs 0) (b 0) (g p) * c'` with `fd_contact_motions.contact/confFactor_pos`.

Before P0.3 (`fderiv_composeFlows_zero`):
- `gp0_composeFlows_single (n Hs hHs i t p) : composeFlows n Hs (Pi.single i t) p = hamFlow (Hs i) t p`
  — induction on `n` with `Fin.cases` on `i`; `Fin.tail (Pi.single 0 t) = 0`,
  `Fin.tail (Pi.single j.succ t) = Pi.single j t`.

## Proof routes (what was actually done vs. the plan)

- **P0.1**: as planned.  `ambient.smooth` = `compositions_smooth ∘ ((s,p) ↦ (s•a, p))` then
  `.contDiffOn`; `zero` = `zero_smul` + `composeFlows_zero`; `diffeo` = `gp0_composeFlows_inv`;
  `support` with `K = ⋃ i, tsupport (hamVF (Hs i))`, compact by `isCompact_iUnion` (finite index
  `Fin n`), fixed points by `gp0_hamFlow_fixed` + `gp0_composeFlows_fixed`; `contact` =
  `gp0_composeFlows_contact`.
- **P0.2**: as planned.  `ContDiff ℝ ∞ (Φ s)` from the `ContDiffOn` on `Icc 0 1 ×ˢ univ` via
  `ContDiffOn.comp` with the slice `p ↦ (s, p)` (`MapsTo` uses `hs`) and `contDiffOn_univ`.
  Injectivity of `DΦ_s(p)` from `fderiv_comp` applied to `Ψ ∘ Φ s = id`.  Curve derivative via
  `HasFDerivAt.comp_hasDerivAt`.  Legendrian: the contact clause times `hLeg θ = 0`.
- **P0.3**: NOT the planned chain-rule induction on `fderiv` in `a`.  Instead a directional
  derivative: `fderiv f 0 (Pi.single i 1)` is the derivative at `t = 0` of `t ↦ f (t • Pi.single i 1)`
  (`HasFDerivAt.comp_hasDerivAt` with `hasDerivAt_id.smul_const`), and by
  `gp0_composeFlows_single` that curve is literally `t ↦ hamFlow (Hs i) t p`, whose derivative at
  `0` is `hamVF (Hs i) (hamFlow (Hs i) 0 p) = hamVF (Hs i) p` (`IsGlobalFlow.hasDerivAt`,
  `hamFlow_zero`).  `HasDerivAt.unique` closes.  ~45 lines instead of ~150.

## Mathlib / Lean pitfalls met

1. `HasFDerivAt.comp_hasDerivAt` produces `HasDerivAt (l ∘ f) …`; matching against a `fun t => l (f t)`
   goal failed with `exact` inline (postponed metavariables) but works as
   `have := hd.comp_hasDerivAt 0 hline; exact this`.  Also the base point must be syntactically
   `(fun t => t • v) 0 = 0 • v`, so restate `hd` at `0 • v` with `simpa using hd`.
2. `Pi.single i t` inside `Fin.tail` needs the ascription `(Pi.single i t : Fin (n+1) → ℝ)`, otherwise
   the dependent-type elaboration of `Fin.tail` fails ("(i : Fin n) → ?m i.succ").
3. `t • Pi.single i (1:ℝ) = Pi.single i t` is closed by `funext k; simp [Pi.single_apply]` alone
   (a following `split_ifs` errors with "no goals").
4. `composeFlows (n+1) Hs b` unfolds by `rfl`/`show` to
   `hamFlow (Hs 0) (b 0) (composeFlows n (Fin.tail Hs) (Fin.tail b) p)`; `composeFlows 0 Hs b = id`
   by `funext fun _ => rfl`.
5. `ContDiff.differentiable` at `∞` takes `(by simp)` for `1 ≤ ∞`, as in `ContactMotions.lean`.
6. The two `alpha`s (GenericFront vs ContactMotions) — see `gp0_alpha_eq`; `rw` with row-86 lemmas
   needs the explicit bridge in both directions.

## For the assembler / executor

- The P0 region is lines 222-395 of `GF_U_P0.lean`; the helpers are all `lemma`s (no `def`), so
  merging is a plain splice between `hamIsotopy_one` and `/-! ### Intermediate genericity stages -/`.
- P1/P3 consumers of P0.3: `gp0_composeFlows_single` may be reused (it is a pointwise identity,
  not just a derivative statement).  P2/P5/P6 consumers of P0.1/P0.2: `gp0_composeFlows_inv`,
  `gp0_composeFlows_contact`, `gp0_contDiff_composeFlows` give inverse/contact/smoothness of
  `composeFlows n Hs b` for arbitrary times `b` (not only `s • a`), which P5.7 (`Φ 1 = composeFlows`)
  and P2.2 may want directly.
- Compile time of the whole file is ~7 s on this pod (imports cached).
