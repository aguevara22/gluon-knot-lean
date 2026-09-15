# Plan: cf:lem-turnlift (tangent lifts and principal turns, row 96) — work/drafts/TurnLift.lean

Source: reference/SM/sm-3-statesum.tex:3542-3578 (proof 3579-3643). Imports the BUILT `SM.TurningNumber`
(DirectionLoop, IsLift/IsSeamLift, exists_lift, lift, tw, tw_int, tw_eq_of_isSeamLift, tw_shift, lift_add_one_sub,
ClosedC1Curve, tangentLoop, rot, normalize) and, through it, the accepted `SM.rotation_number` (RotationTheorem.lean:14).
Scout: work/reports/turning-number-scout-20260913.md §3-4. Check: `cd work/lean && lake env lean ../drafts/TurnLift.lean`.

## Shared device: lifts on intervals
`IsLiftOn u θ a b := ContinuousOn θ (Icc a b) ∧ ∀ s ∈ Icc a b, u s = (cos θ s, sin θ s)` (so `IsSeamLift T θ ↔ IsLiftOn T θ 0 1`
is `Iff.rfl`). Lemmas: `IsLiftOn.increment_eq` (two lifts on `[a,b]`, `a ≤ b`, have equal increments — `constOn_of_comp
isPreconnected_Icc`), `IsLiftOn.increment_eq_zero_of_const` (constant direction ⇒ zero increment), `IsLift.isLiftOn`,
`IsLiftOn.comp` (precompose with a continuous map of `[a,b]` into the domain — reparametrisation of arcs),
`exists_lift_of_unit` (global lift of a continuous unit map on any simply connected, locally path connected space:
`Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts`; used for `ℝ` and `ℝ × ℝ`), `const_of_circleExp_eq_one`
(continuous `g` with `exp (g t) = 1` is constant — `const_of_comp`). Bridge: `circleExp_eq_unitCircle_iff` from TurningNumber.

## Clause → field → model → API

| clause (sm-3 line) | field | model / statement | API |
|---|---|---|---|
| (i-a) 3547 every loop has a lift | `exists_tangent_angle_lift` | `∀ L, ∃ θ, IsSeamLift L.T θ` | `DirectionLoop.exists_seamLift` |
| (i-b) 3548 integer, lift- and seam-independent | `tw_integer`, `tw_lift_independent`, `tw_seam_independent` | `tw_int`; `IsSeamLift L.T θ → tw L = (θ 1 − θ 0)/2π`; `tw (L.shift a) = tw L` | restated from TurningNumber |
| (i-c) 3549 orientation-preserving reparametrisation | `tw_reparam` | `structure Reparam` (`φ : ℝ → ℝ` continuous, `StrictMono`, `φ (s+1) = φ s + 1` — the printed increasing representative); `DirectionLoop.reparam L φ` has `T := L.T ∘ φ`; `tw (L.reparam φ) = tw L` | lift `θ ∘ φ`; `φ 1 = φ 0 + 1`; `lift_add_one_sub` |
| (i-d) 3549-50 homotopy through direction loops | `tw_homotopy` | `structure DirectionHomotopy` (`H : ℝ × ℝ → Plane` continuous, `H (t, s+1) = H (t, s)`, unit); `loop t : DirectionLoop := H (t, ·)`; `tw (h.loop t) = tw (h.loop t')` for all `t t' : ℝ` (a printed `[0,1]`-homotopy extends by `projIcc`) | global lift `Θ` on `ℝ × ℝ`; `g t := Θ(t,1) − Θ(t,0)`, `exp (g t) = 1`, `const_of_comp` |
| (i-e) 3550-51 regular homotopy | `rot_regular_homotopy` | `structure RegularHomotopy` (`Γ Γ' : ℝ × ℝ → Plane`, `Γ` continuous, `HasDerivAt (Γ (t,·)) (Γ' (t,s)) s`, `Γ'` continuous and `≠ 0`, `Γ (t, s+1) = Γ (t, s)`); `curve t : ClosedC1Curve`; `tangentHomotopy : DirectionHomotopy` with `(tangentHomotopy.loop t) = (curve t).tangentLoop` by `rfl`; `(curve t).rot = (curve t').rot` | (i-d), `continuous_normalize_comp`, `deriv_periodic` |
| (i-f) 3551-52 orientation reversal | `rot_reverse` | `ClosedC1Curve.reverse c` (`γ (−s)`, derivative `−γ' (−s)`, chain rule `HasDerivAt.scomp`+`hasDerivAt_neg`); `c.reverse.rot = −c.rot` | lift `θ (−s) + π` (`Real.cos_add_pi`, `sin_add_pi`, `normalize_neg`); `lift_add_one_sub` at `a = −1` |
| (ii) 3553-56 `2π rot L = Σ ϑ_i` | `polygon_two_pi_rot` | `Regular P → 2π · rotationNumber P = Σ principalTurn P i` | `rotationNumber` definition (RotationNumber.lean:10) / `rotation_number` .1 |
| (ii) 3557-60 path constancy, subdivision, reversal, triangles | `polygon_path_constant`, `polygon_subdivision`, `polygon_reversal`, `polygon_triangle` | exact forms of `SM.rotation_number` clauses 3, 4 (regular + value), 5-6, 7 (`rotationNumber P = turn P i`, `= ±1`) | `SM.rotation_number` (not re-proved) |
| (iii-a) 3561-63 corner rounding | `rounding` | curve `γ : ClosedC1Curve`, breakpoints `a b : ℕ → ℝ`, `a 0 = 0`, `a n = 1`, `a k ≤ b k ≤ a (k+1)` for `k < n`; on `[a k, b k]` the corner arc at vertex `k` has a lift of increment `principalTurn L k` (some `IsLiftOn` — "compatible lift"); on `[b k, a (k+1)]` `T_γ = normalize (edge L k)` (straight piece); conclusion `γ.rot = rotationNumber L` | telescoping `Finset.sum_range_sub`, `increment_eq`, `increment_eq_zero_of_const`, reindex `range n → ZMod n` by `Finset.sum_nbij'` (`ZMod.val`) |
| (iii-b) 3565-73 arc replacement | `replacement` | closed curves `Fb Fc : ClosedC1Curve`; after a seam shift the arc occupies `[0, λ]` resp. `[0, μ]` (`λ μ ∈ [0,1]`); the complementary arc is shared up to a monotone continuous reparametrisation `ψ` of `[λ,1]` onto `[μ,1]` (`ψ λ = μ`, `ψ 1 = 1`, `Fb.tangentLoop.T s = Fc.tangentLoop.T (ψ s)`); `θb`, `θc` lifts on the arcs with increments `Δb, Δc`; `Fc.rot − Fb.rot = (Δc − Δb)/2π` (equal initial values are irrelevant: only increments enter; same endpoints / tangent rays are encoded by `Fb, Fc` being closed `C¹`) | `increment_eq`, `IsLiftOn.comp`, additivity of one global lift |
| (iii-c) 3574-77 GL⁺ path | `glplus_invariance` | `structure GLPlusPath` (entries `a b c d : ℝ → ℝ` continuous, `a d − b c > 0`, value `I` at `0`; `apply t z`); arcs as nonzero continuous tangent paths `vb vc : ℝ → Plane` with the same oriented rays at `0` and `1` (`vc 0 = r • vb 0`, `r > 0`, same at `1`); lifts of `normalize ∘ vb`, `normalize ∘ vc` and of `normalize ∘ (A.apply 1 ∘ vb)`, `… vc` on `[0,1]`; `Δc' − Δb' = Δc − Δb` | `pair_increment_sub_const`: two unit homotopies `U V : ℝ × ℝ → Plane` agreeing at `s = 0, 1` have `incr U(t,·) − incr V(t,·)` constant in `t` (the printed loop "c then b backwards" without the concatenation); `normalize_smul_pos`, `apply_smul`, `apply_ne_zero`, `fun_prop` |

Bundle `TurnLiftData : Prop`, `theorem turnlift : TurnLiftData`, `#print axioms SM.turnlift` (expect propext, Classical.choice, Quot.sound).
Method note: lifts come from Mathlib's covering-space lifting (as in TurningNumber), not the printed atan2 subdivision;
(iii-c) uses the pair-homotopy lemma directly (the printed concatenated loop is not constructed). Statements are the printed ones.

## Result (2026-09-13)
`cd work/lean && lake env lean ../drafts/TurnLift.lean`: no errors, no warnings, 0 `sorry`, 652 lines, ~4.5 s;
`#print axioms SM.turnlift` = [propext, Classical.choice, Quot.sound]. Nothing written under work/lean. All three
clauses delivered; the only hypotheses in bundle fields that the underlying lemmas do not need are the printed
normalisations (`StrictMono φ` in `Reparam`, `MonotoneOn ψ`/`mu ≤ 1`/`θb 0 = θc 0` in `replacement`, `Regular L`/`3 ≤ n`
in `rounding`, `3 ≤ n` in `polygon_two_pi_rot`). Bonus: `ClosedC1Curve.tangentLoop_T_eq_of_eventuallyEq` derives the
direction-level hypothesis of (iii-b) from a curve-level C¹ reparametrisation with positive derivative.
