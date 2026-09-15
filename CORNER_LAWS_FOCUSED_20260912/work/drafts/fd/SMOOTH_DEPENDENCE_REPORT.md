# SMOOTH_DEPENDENCE_REPORT.md — `SM.SmoothDependence` proved (row 86 fd:contact-motions)

Written 2026-09-14 (work/drafts/fd/).  Closes the one explicit hypothesis of `ContactMotions.lean`:
smooth dependence of an ODE flow on the initial point, absent from Mathlib at this pin
(`Mathlib/Analysis/ODE/*` has Picard–Lindelöf, uniqueness, Grönwall, time regularity only;
`Mathlib/Analysis/Calculus/FDeriv/Partial.lean` exists but contains no flow result).

| item | value |
|---|---|
| deliverable | `work/drafts/fd/SmoothDependence.lean` — **652 lines, 0 errors, 0 warnings, no placeholder declaration**, compile ≈ 7 s (`cd work/lean && lake env lean ../drafts/fd/SmoothDependence.lean`) |
| main theorem | `SM.SmoothDep.contDiff_uncurry` : for `E : Type` finite-dimensional real normed, `X : E → E` `C^∞` compactly supported, `φ` a global flow of `X` ⇒ `ContDiff ℝ ∞ (uncurry φ)` |
| the row's statement | `SM.smoothDependence_of_flow` (structure-free: hypotheses `∀ p, φ 0 p = p` and `∀ s p, HasDerivAt (fun s => φ s p) (X (φ s p)) s`) and `SM.smoothDependence_of_isGlobalFlow` (literally the body of `SM.SmoothDependence` with the copied structure `SmoothDep.IsGlobalFlow`) |
| axioms (`#print axioms` on a /tmp copy) | `[propext, Classical.choice, Quot.sound]` for `hasFDerivAt_flow_of_variational`, `spaceSmooth`, `contDiff_space`, `contDiff_uncurry`, `smoothDependence_of_flow`, `smoothDependence_of_isGlobalFlow` |
| what remains | **nothing** — the full `C^∞` result is proved; no isolated induction step, no extra hypothesis |
| **final module for porting** | `work/drafts/fd/ContactMotionsFinal.lean` (1,437 lines): `ContactMotions.lean` + this file's §2–8 (module §7–§13); `SM.fd_contact_motions : SM.ContactMotionsData` unconditional (line 1434), `SM.smoothDependence : SM.SmoothDependence` (line 1430), `SM.fd_contact_motions_of_smoothDependence` (line 905); 0 errors, standard axioms; statement part lines 130–894 byte-identical to `ContactMotions.lean` up to two docstring edits; 0 name clashes with `work/lean` (see `FD_84_86_REPORT.md` §4) |
| merge test (superseded by the final module) | `work/drafts/fd/ContactMotions_SmoothDependence_MERGED.lean` (1,411 lines) = `ContactMotions.lean` + §2–8 of this file re-targeted at `ContactMotions.IsGlobalFlow`, ending in `SM.smoothDependence : SM.SmoothDependence` and `SM.fd_contact_motions_unconditional : SM.ContactMotionsData`; 0 errors, same three axioms |

## 1. Statement proved

`ContactMotions.lean` line 832:
```lean
def SmoothDependence : Prop :=
  ∀ X : ℝ³ → ℝ³, ContDiff ℝ ∞ X → HasCompactSupport X →
    ∀ φ : ℝ → ℝ³ → ℝ³, IsGlobalFlow X φ → ContDiff ℝ ∞ (uncurry φ)
```
`SmoothDependence.lean` proves (namespace `SM`):
```lean
theorem smoothDependence_of_isGlobalFlow :
    ∀ X : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), ContDiff ℝ ∞ X →
      HasCompactSupport X → ∀ φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        SmoothDep.IsGlobalFlow X φ → ContDiff ℝ ∞ (Function.uncurry φ)
```
where `SmoothDep.IsGlobalFlow` is a verbatim copy (same two fields, same order) of
`ContactMotions.IsGlobalFlow`, and the general theorem behind it is
```lean
theorem SmoothDep.contDiff_uncurry {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : E → E} {φ : ℝ → E → E} (hX : ContDiff ℝ ∞ X)
    (hc : HasCompactSupport X) (hφ : IsGlobalFlow X φ) : ContDiff ℝ ∞ (uncurry φ)
```
(`E : Type`, not `Type*`, because the induction quantifies over the spaces `E × (E →L[ℝ] E)` and
`ℝ × E`; `ℝ³ : Type`, so this is all the row needs.)

## 2. Choice of packaging (why a copy, not an import)

The file imports nothing from `work/drafts`, as required.  §1 of the file (105 lines) copies
`ContactMotions.lean` §2 verbatim under `SM.SmoothDep`: `IsGlobalFlow`, `ODE_unique_global`,
`ODE_unique_Ioo`, `exists_solution_Ioo`, `exists_solution_global`, `exists_isGlobalFlow`
(existence of a global flow of a bounded globally Lipschitz field on a complete space — needed
here for the *augmented* spaces, so the general-`E` form is essential).  §4 generalises the three
`ℝ³`-specific lemmas of `ContactMotions.lean` §3 to any normed space (`exists_bound_of_hasCompactSupport`,
`exists_lipschitzWith_of_hasCompactSupport`, `exists_isGlobalFlow_of_hasCompactSupport` — same
proofs, `[CompleteSpace E]` instead of `ℝ³`).  Everything else (§2–§3, §5–§8, ≈ 520 lines) is new.

**Merge recipe (verified by the MERGED file):**
1. add `import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension` and
   `import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension` to `ContactMotions.lean`;
2. paste §2–§7 of `SmoothDependence.lean` into `namespace SM.ContactMotions` (so that the
   `namespace IsGlobalFlow` lemmas `neg`, `dist_le_nonneg`, `dist_le`, `lipschitzWith_space`,
   `continuous_space` attach to `ContactMotions.IsGlobalFlow`); drop the duplicate
   `continuous_time`; prime the three general-`E` §4 lemma names (or generalise the `ℝ³` ones);
3. `theorem smoothDependence : SmoothDependence := fun _ hX hc _ hφ => ContactMotions.contDiff_uncurry hX hc hφ`
   and `fd_contact_motions smoothDependence : ContactMotionsData`.
The MERGED draft is exactly this, generated mechanically, and compiles.

## 3. Route (as proved; section numbers are the file's)

**§2 Time reversal and Lipschitz dependence.**  `IsGlobalFlow.neg`: `(s, p) ↦ φ (-s) p` is a
global flow of `-X` (`HasDerivAt.scomp` with `hasDerivAt_neg`).  Every estimate below is proved
forward in time on `[0, T]` and reflected with `neg`.  `IsGlobalFlow.dist_le_nonneg`:
`dist (φ s p) (φ s q) ≤ dist p q · e^{K s}` for `s ≥ 0`, directly from Mathlib's
`dist_le_of_trajectories_ODE` (Grönwall for two exact solutions); `dist_le` for all `s` with `|s|`;
`lipschitzWith_space`, `continuous_space`.

**§3 The variational estimate — `hasFDerivAt_flow_of_variational`** (the analytic core, ≈ 100 lines).
Hypotheses: `X` differentiable, `‖fderiv ℝ X x‖₊ ≤ K` for all `x`, `UniformContinuous (fderiv ℝ X)`,
`φ` a global flow, `T ≥ 0`, `p`, and `D : ℝ → E →L[ℝ] E` with `D 0 = 1` and
`HasDerivAt D ((fderiv ℝ X (φ t p)).comp (D t)) t` for `t ∈ [0, T]`.  Conclusion:
`HasFDerivAt (φ T) (D T) p`.  Proof: by `hasFDerivAt_iff_isLittleO_nhds_zero` and
`Asymptotics.isLittleO_iff`, fix `c > 0`; take `η` with `η e^{KT} e^{(K+1)T} = c` and `δ` from
`Metric.uniformContinuous_iff` for `fderiv ℝ X` at `η`; for `‖h‖ < δ e^{-KT}` the error curve
`f t = φ t (p+h) − φ t p − D t h` has `f 0 = 0`, derivative
`X(φ t (p+h)) − X(φ t p) − DX(φ t p)(D t h)` (`HasDerivAt.sub`, `HasDerivAt.clm_apply`), which is
rewritten as `[X(y+u) − X(y) − DX(y) u] + DX(y)(f t)` with `y = φ t p`, `u = φ t (p+h) − y`.
The bracket is `≤ η ‖u‖` by the mean value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` on `closedBall y ‖u‖` (where
`‖DX z − DX y‖ ≤ η` since `‖u‖ ≤ ‖h‖ e^{KT} < δ` by §2), so
`‖f'‖ ≤ (K+1)‖f‖ + η e^{KT}‖h‖`; Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` with
`δ = 0` and the elementary bound `gronwallBound 0 (K+1) ε T ≤ ε e^{(K+1)T}`
(`gronwallBound_zero_le`, from `gronwallBound_of_K_ne_0`) give `‖f T‖ ≤ c ‖h‖`.

**§4 Compactly supported `C^1` fields.**  Bounded (`HasCompactSupport.isCompact_range`), derivative
bounded (`HasCompactSupport.fderiv`), globally Lipschitz (`lipschitzWith_of_nnnorm_fderiv_le`),
derivative uniformly continuous (`HasCompactSupport.uniformContinuous_of_continuous`, Heine–Cantor),
global flow exists (§1), `fderiv = 0` off the support.

**§5 The augmented system with a cut-off.**  On `F = E × (E →L[ℝ] E)` (finite-dimensional by
`ContinuousLinearMap.instModuleFinite`, hence `HasContDiffBump` and complete),
`augFieldCut X b (x, A) = (b A • X x, b A • (fderiv ℝ X x).comp A)` with `b : ContDiffBump (0 : E →L[ℝ] E)`.
It is `C^∞` (`ContDiff.smul`, `ContDiff.clm_comp`, `ContDiff.fderiv_right`) and compactly supported
(support ⊆ `tsupport X ×ˢ tsupport b`; the cut-off in `A` is what makes the pair compactly
supported — cutting off only the second component would leave `(X x, 0)` for large `A`).  Its
second component is bounded by `‖DX(x)‖ ‖A‖` (`0 ≤ b ≤ 1`, `opNorm_comp_le`).

**§6 Induction on the order — `SpaceSmooth k`, `spaceSmooth`.**
`SpaceSmooth k := ∀ E X φ s, … → ContDiff ℝ k (φ s)` (all finite-dimensional `E : Type`).
`spaceSmooth_zero` is §2.  `contDiff_space_succ_nonneg` (the step, `s ≥ 0`, ≈ 75 lines): with
`R = e^{K s}` and `b` equal to `1` on `closedBall 0 R`, let `Ψ` be a global flow of `augFieldCut X b`
(§4) and `γ t = Ψ t (p, 1)`.  Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`, `δ = 1`,
`ε = 0`, `gronwallBound_ε0`) gives `‖γ₂ t‖ ≤ e^{K t} ≤ R` on `[0, s]`, so `b (γ₂ t) = 1` there
(`ContDiffBump.one_of_mem_closedBall`); then `γ₁` solves `X`'s ODE on `[0, s]` and equals `φ t p`
by forward uniqueness (`dist_le_of_trajectories_ODE` with `δ = 0`), and `γ₂` solves the variational
equation along `φ · p`.  §3 gives `HasFDerivAt (φ s) (Ψ s (p, 1)).2 p` for every `p`, so
`fderiv ℝ (φ s) = fun p => (Ψ s (p, 1)).2`, which is `C^k` by the induction hypothesis applied to
`Ψ` on `F`; `contDiff_succ_iff_fderiv` concludes.  `spaceSmooth_succ` handles `s < 0` by `neg`.
`contDiff_space`: `φ s ∈ C^∞` for every `s` (`contDiff_infty`).

**§7 Joint smoothness by suspension — `contDiff_uncurry`.**  Instead of a "continuous partial
derivatives ⇒ jointly differentiable" argument (not in Mathlib; would need its own mean-value
bookkeeping at every order), time is turned into a space variable: for a bump `b` on `ℝ` with
`b = 1` on `[-R, R]`, `R = |s₀| + 1`, the field `suspField X b (τ, x) = (0, (b τ * τ) • X x)` on
`ℝ × E` is `C^∞` compactly supported, and `(s, (τ, x)) ↦ (τ, φ (b τ * τ * s) x)` is a global flow
of it (`isGlobalFlow_suspFlow`, a two-line check).  By §6 its **time-one map**
`(τ, x) ↦ (τ, φ (b τ * τ) x)` is `C^∞`; on `{|τ| < R}` it is `(τ, φ τ x)`, so `uncurry φ` is
`C^∞` at `(s₀, p₀)` (`ContDiffAt.congr_of_eventuallyEq`), and `contDiff_iff_contDiffAt` finishes.

**§8** The two `ℝ³` statements.

## 4. Mathlib lemmas that carried the proof

`dist_le_of_trajectories_ODE`, `norm_le_gronwallBound_of_norm_deriv_right_le`,
`gronwallBound_of_K_ne_0`, `gronwallBound_ε0` (Analysis/ODE/Gronwall);
`IsPicardLindelof.of_time_independent`, `exists_eq_forall_mem_Icc_hasDerivWithinAt₀`,
`ODE_solution_unique_univ`, `ODE_solution_unique_of_mem_Ioo` (via the copied §1);
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, `lipschitzWith_of_nnnorm_fderiv_le`
(Calculus/MeanValue); `hasFDerivAt_iff_isLittleO_nhds_zero`, `Asymptotics.isLittleO_iff`;
`HasDerivAt.clm_apply`, `HasDerivAt.scomp`, `HasDerivAt.prodMk`, `HasFDerivAt.comp_hasDerivAt`;
`contDiff_succ_iff_fderiv`, `contDiff_infty`, `contDiff_zero`, `contDiff_iff_contDiffAt`,
`ContDiffAt.congr_of_eventuallyEq`, `ContDiff.fderiv_right`, `ContDiff.clm_comp`, `ContDiff.smul`;
`ContDiffBump` (`contDiff`, `hasCompactSupport`, `one_of_mem_closedBall`, `nonneg`, `le_one`) with
the finite-dimensional `HasContDiffBump` instance (BumpFunction/FiniteDimension);
`HasCompactSupport.uniformContinuous_of_continuous`, `HasCompactSupport.fderiv`,
`HasCompactSupport.intro`, `HasCompactSupport.comp_left`, `image_eq_zero_of_notMem_tsupport`;
`ContinuousLinearMap.instModuleFinite`, `FiniteDimensional.proper_real` (completeness);
`Metric.uniformContinuous_iff`, `ContinuousLinearMap.opNorm_comp_le`, `le_opNorm`, `norm_id_le`.

## 5. Line counts

| part | lines | status |
|---|---|---|
| header docstring | 56 | — |
| §1 copied from `ContactMotions.lean` §2 (`IsGlobalFlow`, uniqueness, existence) | 105 | verbatim copy |
| §2 time reversal, Lipschitz dependence | 50 | new |
| §3 variational estimate (`gronwallBound_zero_le`, `hasFDerivAt_flow_of_variational`) | 115 | new |
| §4 compactly supported `C^1` fields (3 lemmas generalised from `ContactMotions.lean` §3, 3 new) | 50 | adapted / new |
| §5 augmented field with cut-off | 40 | new |
| §6 induction `SpaceSmooth`, step, `contDiff_space` | 125 | new |
| §7 suspension, `contDiff_uncurry` | 70 | new |
| §8 the `ℝ³` statements | 25 | new |
| **total** | **652** | 0 errors, 0 warnings |

Estimated in `FD_84_86_FEASIBILITY.md` at 4 000–6 000 lines; the two devices that made it ≈ 550 new
lines were (a) the cut-off augmented field, which keeps every field compactly supported so that all
estimates are global and the existence theorem of `ContactMotions.lean` applies at every level, and
(b) the suspension trick, which obtains joint smoothness from space-smoothness of a time-one map.

## 6. Checker / row notes

* No declaration named `SmoothDependence` is redefined; `SM.SmoothDependence` stays the row's
  hypothesis name in `ContactMotions.lean` until merged, when
  `theorem SM.smoothDependence : SM.SmoothDependence` closes it and
  `fd_contact_motions smoothDependence : ContactMotionsData` makes row 86 unconditional.
* The checker-enforced names of row 86 (if any beyond `SM.fd_contact_motions`) are unaffected.
* Draft files in work/drafts/fd/ each compile alone; `ContactMotions_SmoothDependence_MERGED.lean`
  duplicates `ContactMotions.lean` by construction and should be deleted after the merge.
