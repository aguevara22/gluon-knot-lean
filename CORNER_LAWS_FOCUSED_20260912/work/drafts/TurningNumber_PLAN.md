# Plan: cf:def-turning (direction loops and smooth rotation) — work/drafts/TurningNumber.lean

Source: reference/SM/sm-3-statesum.tex:3514-3541 (SM cf:def-turning); identical text in CV def:rot, paragraph
"Direction loops and smooth curves", reference/R/CV/d1_setup.tex:767-787. Decision F6 (work/reports/cv-lane-plan-20260913.md:168-174):
define ONCE here (SM), CV rows 144/145 re-export. Design and verified APIs: work/reports/turning-number-scout-20260913.md §2-3;
prototypes /workspace/scratch/scout3.lean, scout4.lean, scout5.lean (reused verbatim where possible).

## Printed sentence -> Lean object (API used)

| # | printed (sm-3 line) | Lean | API |
|---|---|---|---|
| D1 | 3515-16 direction loop `T : ℝ/ℤ → S¹` | `structure DirectionLoop` (`T : ℝ → Plane`, `Continuous T`, `Function.Periodic T 1`, `∀ s, euclideanLength (T s) = 1`); bridge `DirectionLoop.toCircle : C(ℝ, Circle)` via `unitCircle u hu := ⟨planeComplex u, _⟩` | `mem_sphere_zero_iff_norm`, `Continuous.subtype_mk`, `SM.continuous_planeComplex` |
| D2 | 3516-18 tangent-angle lift at a seam, `θ : [0,1] → ℝ` continuous, `T s = (cos θ s, sin θ s)` | `IsSeamLift T θ := ContinuousOn θ (Icc 0 1) ∧ ∀ s ∈ Icc 0 1, T s = (Real.cos (θ s), Real.sin (θ s))`; global proof device `IsLift T θ` (Continuous, all s) | `circleExp_planeComplex : (Circle.exp θ : ℂ) = planeComplex (cos θ, sin θ)` (`Circle.coe_exp`, `Complex.ext`) |
| D7a | 3530-32 "the lemma that follows constructs the lift" | `DirectionLoop.exists_lift : ∃ θ, IsLift L.T θ` (hence `∃ θ, IsSeamLift L.T θ`); `DirectionLoop.lift := Classical.choose` | `Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts` (ℝ simply connected + locally path connected: imports Convex.Contractible, SimplyConnected, LocallyConvex), `Circle.surjOn_exp_neg_pi_pi` |
| D3 | 3519-21 `tw(T) = (θ(1) − θ(0))/2π` | `tw L : ℝ := (L.lift 1 - L.lift 0) / (2π)`; `tw_eq_of_isSeamLift : IsSeamLift L.T θ → tw L = (θ 1 - θ 0)/(2π)` (so the value is the printed one for ANY seam lift); `tw_int : ∃ k : ℤ, tw L = k` | `IsCoveringMap.constOn_of_comp isPreconnected_Icc`, `Circle.exp_sub`, `Circle.exp_eq_exp` |
| D7b | 3532-33 "do not depend on its choice, on the seam" | `seamLift_increment_eq` (choice); `DirectionLoop.shift L a` (T(·+a)) and `tw_shift : tw (L.shift a) = tw L` (seam) | `IsCoveringMap.const_of_comp` on `s ↦ θ(s+1) − θ s` |
| D4 | 3522-27 closed C¹ regular oriented curve, `γ' ≠ 0`; `T_γ = γ'/|γ'|`, `rot(γ) = tw(T_γ)` | `structure ClosedC1Curve` (`γ γ' : ℝ → Plane`, `∀ t, HasDerivAt γ (γ' t) t`, `Continuous γ'`, `∀ t, γ' t ≠ 0`, `Function.Periodic γ 1`); `deriv_periodic`; `normalize v := (euclideanLength v)⁻¹ • v`; `ClosedC1Curve.tangentLoop : DirectionLoop`; `ClosedC1Curve.rot := tw c.tangentLoop` | `HasDerivAt.scomp`, `HasDerivAt.unique`, `Continuous.inv₀`, `euclideanLength_pos`, `planeComplex_smul`, `norm_smul` |
| D5 | 3528-29 polygon in the regular locus: rot remains that of lem:rot | no new object: the polygon rotation IS the accepted `SM.rotationNumber` (RotationNumber.lean:10); bundle field cites `SM.rotation_number` (RotationTheorem.lean:14) clauses: `rotationNumber P = (1/2π) Σ principalTurn P i` and integrality | `SM.rotation_number` |
| D6 | 3529-30 `R(L) = |rot(L)|` for either | `ClosedC1Curve.R c := |c.rot|`; `polygonR P := |rotationNumber P|` | — |
| D7c | 3533-34 "or on an orientation-preserving regular reparametrisation" | NOT here: it is clause (i-c) of cf:lem-turnlift (row 96, unit U2 of the scout plan), needs the reparametrisation model | — |

## Bundle `TurningDefinitionData : Prop` (one field per printed sentence) and `theorem turning_definition`
direction_loop (D1 unfolding + circle bridge), tangent_angle_lift (D2, `Iff.rfl`), exists_tangent_angle_lift (D7a, the
existence making tw well defined), tw_eq (D3, for every seam lift), tw_integer, closed_curve (D4 unfolding + γ' periodic),
tangent_loop (`T_γ` pointwise + unit length), rot_curve (`rfl`), polygon_rot (D5 via `rotation_number`), R_eq (D6, both kinds),
lift_and_seam_independent (D7b). Ends with `#print axioms SM.turning_definition` — expected [propext, Classical.choice, Quot.sound].

## Method note
Existence of the lift uses Mathlib's covering-space lifting through `Circle.exp` instead of the printed atan2 subdivision
(sm-3:3580-3620 belongs to the lemma's proof, not to the definition); the checked object is the printed statement.
`tw` is ℝ-valued with an integrality theorem, as `SM.rotationNumber` is; `CV.rot : ℤ` connects by cast (CV.rot_eq_rotationNumber).
Check: `cd work/lean && lake env lean ../drafts/TurningNumber.lean`.

## Result (2026-09-13)
`cd work/lean && lake env lean ../drafts/TurningNumber.lean`: no errors, no warnings, 0 `sorry`, 347 lines, ~4.4 s;
`#print axioms SM.turning_definition` = [propext, Classical.choice, Quot.sound]. Nothing written under work/lean.
Toolchain note: `continuous_add_right` is deprecated here; use `continuous_add_const`.
