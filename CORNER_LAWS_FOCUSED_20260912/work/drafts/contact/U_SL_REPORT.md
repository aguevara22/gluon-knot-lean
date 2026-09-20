# U_SL_REPORT — unit SL (PLAN_FINAL §6 U1: `u_sl_radius`, `u_sl_family`, `u_sl_reparam`, `u_sl_isotopy`)

Prover, 2026-09-15.  File: `work/drafts/contact/U_SL.lean` (= `Skeleton_FINAL.lean` with the four SL
leaves closed and 11 helpers `usl_*` inserted inside §5.4; every other line byte-identical — `diff
Skeleton_FINAL.lean U_SL.lean` touches only skeleton lines 552-560).

Compile: `cd work/lean && lake env lean ../drafts/contact/U_SL.lean` — **0 errors**, exit 0; the only
warnings are `declaration uses sorry` at the seven leaves of the other units (`u_circle`,
`u_legendrianFront`, `u_spatialOf`, `u_reading`, `u_transport`, `u_regular`, `u_family`).
`grep -c sorry`: 12 before → 8 after (line 19 of the module docstring + the 7 foreign leaves).

Axiom footprint (`#print axioms`, checked on a copy): `u_sl_radius`, `u_sl_family`, `u_sl_reparam`,
`u_sl_isotopy` each depend on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no
literature axiom (row 88 `fd_linking_calculus` is fully proved in the accepted layer).

## 1. Leaves

| leaf | status | route |
|---|---|---|
| `u_sl_radius` (U1a) | PROVED | `slCircle T = selfLinking (2π) T ε₁` by `↓reduceDIte` (`usl_slCircle_eq`); `self_linking_invariant` on the constant family twice, with `ε₀ := ε₁` (disjointness from `transverse_uniform`'s spec) and `ε₀ := ε` (the hypothesis), both compared with `min ε ε₁`, `s = s' = 0`. |
| `u_sl_family` (U1b) | PROVED | `transverse_uniform` gives `ε₀`; U1a at `s` and `s'` with radius `ε₀`; `self_linking_invariant` with `ε = ε' = ε₀`. |
| `u_sl_reparam` (U1c) | PROVED | the family `ρ_s = (1−s)·id + s·ρ`, `T ∘ ρ_s`, is a `TransverseFamily (2π)` (`usl_reparam_family`); `u_sl_family` at `s = 1, 0`; `simp only [sub_self, …]` identifies the ends with `T ∘ ρ` and `T`. |
| `u_sl_isotopy` (U1) | PROVED | strip family `F` of `TransverselyIsotopic` composed with the clock `Real.smoothTransition` is a `TransverseFamily (2π)` on `ℝ × ℝ` (`usl_isotopy_family`, `ContDiffOn.comp_contDiff`); `u_sl_family` at `0, 1` gives `slCircle T₀ = slCircle (T₁ ∘ ρ)`; `u_sl_reparam` finishes — AFTER deriving `IsPositiveTransverseEmbedding (2π) T₁` (see §3). |

No leaf is false; none needs a stronger hypothesis.  The leaves are used in the order of §5.4
(`u_sl_family` uses `u_sl_radius`; `u_sl_reparam` uses `u_sl_family`; `u_sl_isotopy` uses both).

## 2. Helpers added (all prefixed `usl_`, placed immediately before the first leaf that uses them)

Before `u_sl_radius`:
* `usl_slCircle_eq` — `slCircle T = selfLinking (2π) T (Classical.choose …)` on the class (the `dite` reduced).
* `usl_contactForm_smul` — `lcContactForm p (c • w) = c * lcContactForm p w` (shared by U1c and U1).
* `usl_disjoint_of_uniform` — the `DisjointPair` clause of `transverse_uniform` in the `∀ u u', pushoff … u ≠ T s u'` form `self_linking_invariant` consumes (`disjoint u' u`: note the argument order of `DisjointPair.disjoint : ∀ u v, C₂ v ≠ C₁ u`).

Before `u_sl_reparam`:
* `usl_reparam_lift_int` — `ρ (θ + k·2π) = ρ θ + k·2π` for every `k : ℤ` (`ρ − id` is `2π`-periodic, `Periodic.int_mul`).
* `usl_reparam_family` — `TransverseFamily (2π) (fun s θ => T ((1 − s) θ + s ρ θ))`: `ρ_s′ = (1−s) + s ρ′ > 0` on `[0,1]`, `StrictMono` (`strictMono_of_deriv_pos`) gives the embedded clause from `T`'s, chain rule `deriv.scomp` + `usl_contactForm_smul` gives positivity, `fun_prop` gives joint smoothness.

Before `u_sl_isotopy`:
* `usl_reparam_strictMono`, `usl_reparam_surjective` — `ρ` is a strictly monotone bijection of `ℝ` (`Continuous.surjective` with `Monotone.tendsto_atTop_atTop / atBot_atBot`, unboundedness from the lift and `exists_nat_ge`).
* `usl_reparam_exists_inverse` — a smooth two-sided inverse `σ` of `ρ` (`StrictMono.orderIsoOfSurjective` → `OrderIso.toHomeomorph` → `Homeomorph.contDiff_symm_deriv` with `f' = deriv ρ ≠ 0`).
* `usl_embedding_of_circle` — row 84's `IsEmbeddedCircle T ∧ IsPositiveTransverse T` is row 88's `IsPositiveTransverseEmbedding (2π) T` (`2πk` vs `k·2π`).
* `usl_transverseEmbedding_of_comp` — `IsCircleReparam ρ → IsPositiveTransverseEmbedding (2π) (T ∘ ρ) → IsPositiveTransverseEmbedding (2π) T` (smoothness through `σ`; periodicity, embeddedness through the lift; positivity `α((T∘ρ)′) = ρ′ · α(T′∘ρ)`, `pos_of_mul_pos_right`).
* `usl_isotopy_family` — the clocked strip family is a `TransverseFamily (2π)`.

Total inserted: ~230 lines (plan estimate 450).

## 3. What the assembler / executor must know

1. **Hidden step in U1 (not in PLAN §6's U1 text).**  `slCircle T₁` is defined by cases on
   `IsPositiveTransverseEmbedding (2π) T₁`, and `u_sl_reparam` needs that predicate for `T₁` itself, but
   `TransverselyIsotopic T₀ T₁` only supplies it for the END `F 1 = T₁ ∘ ρ`.  The leaf is TRUE as stated
   (`ρ` is a diffeomorphism of the circle), but closing it requires the smooth inverse of `ρ`
   (`usl_reparam_exists_inverse`, `usl_transverseEmbedding_of_comp`) — ~90 of the 230 lines.  No statement
   was changed; nothing is needed from other units.
2. `fd_contact_of_units` consumes only `u_sl_isotopy` (twice: `hiso` from row 84, `transverselyIsotopic_ofGF hiso2`
   from row 87); U1a-c are internal to the unit but are stated as separate Props in the skeleton and are all proved.
3. The helpers are reusable by U0/U6: `usl_embedding_of_circle` (TN ↔ LC class bridge),
   `usl_transverseEmbedding_of_comp` / `usl_reparam_exists_inverse` (inverse of an `IsCircleReparam`), and
   `usl_contactForm_smul`.
4. When porting to `SM/FdContactUnits*.lean`: the block needs only the imports of the skeleton; `open Set
   Function Real` and `open scoped ContDiff` (for `∞`) as in the skeleton preamble; `IsCircleReparam`,
   `IsEmbeddedCircle`, `IsPositiveTransverse`, `TransverselyIsotopic` are `SM.TransverseNeighborhood.*`
   (opened namespace), not the `GenericFront.*` copies.

## 4. Mathlib pitfalls met (v4.34.0-rc2 pin)

* `dif_pos` is DEPRECATED (warning "use `dite_eq_left`"); the clean way to reduce `slCircle` on its domain is
  `simp only [slCircle, hT, ↓reduceDIte]` (as `src_contact_iff_consequence` already does).
* `simpa using h1.add h2` for `HasDerivAt.add` fails: simp normalizes `fun x => f x + g x` to Pi-addition `f + g`
  AND the `AddCommGroup ℝ` instance paths differ (`normedAddCommGroup.toAddCommGroup` vs `instAddCommGroup`), so
  `simpa` cannot close by syntactic match.  Use `have := h1.add h2; rw [mul_one] at this; exact this`
  (`exact` checks defeq and unifies the instances).
* `(hper.int_mul k) θ` for `Periodic` is ALREADY beta-reduced: `simp only at this` fails with "no progress".
  State the instance explicitly: `have h : ρ (θ + k * (2π)) - (θ + k * (2π)) = ρ θ - θ := hper.int_mul k θ`.
* `Real.smoothTransition.contDiff : ∀ {n : ℕ∞}, ContDiff ℝ ↑n smoothTransition` — unifies with `∞` (`↑⊤`)
  without annotation; `.zero`, `.one`, `.nonneg`, `.le_one` are the endpoint / range lemmas.
* Smooth inverse of a monotone bijection of `ℝ`: `Homeomorph.contDiff_symm_deriv (f : ℝ ≃ₜ ℝ) (h₀ : ∀ x, f' x ≠ 0)
  (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : ContDiff ℝ n f) : ContDiff ℝ n f.symm`; the homeomorphism from
  `StrictMono.orderIsoOfSurjective ρ hmono hsurj |>.toHomeomorph`, whose coercion is `ρ` by
  `OrderIso.coe_toHomeomorph` + `StrictMono.coe_orderIsoOfSurjective`.  Pack it as `obtain ⟨e, he⟩ : ∃ e : ℝ ≃ₜ ℝ,
  ⇑e = ρ` so the goals do not carry the `let`.
* `deriv.scomp x hg hh : deriv (g ∘ h) x = deriv h x • deriv g (h x)` (vector-valued `g`); `Function.comp` vs
  `fun θ => T (ρ θ)` is defeq, `exact`/`show` accept it, `rw` does not — use `show` with the beta-reduced form
  when the goal carries `(fun s θ => …) s`.
* `fun_prop` proves `ContDiff ℝ ∞ (fun p : ℝ × ℝ => (1 - p.1) * p.2 + p.1 * ρ p.2)` given `hρ.smooth` in
  context (`have := hρ.smooth`).
