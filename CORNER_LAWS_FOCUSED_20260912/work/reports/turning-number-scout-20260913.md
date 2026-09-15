# Turning-number scout — direction loops, tangent-angle lifts, smooth rotation (2026-09-13)

Scope: the shared unit behind SM cf:def-turning (row 95), SM cf:lem-turnlift (row 96), CV def:rot
"Direction loops and smooth curves" (row 144) and CV lem:turnlift (i),(iii) (row 145). Plan decision
F6 (work/reports/cv-lane-plan-20260913.md:168–174, 526–575): define ONCE in SM, re-export in CV.
Polygon clause (ii) is done: `CV.turnlift_ii`, `CV.rotRay_indep`, `CV.rot_eq_rotationNumber`,
`CV.turnlift_ii_data` (work/lean/CV/Rotation.lean:344–615). All API names below were verified by
grep in work/lean/.lake/packages/mathlib and by elaborating /tmp/scout{1..5}.lean with
`lake env lean` (Lean v4.34.0-rc2, Mathlib 85e3a25e; ~5 s per file, no `lake build`).

## 1. Printed text, itemized

SM cf:def-turning (reference/SM/sm-3-statesum.tex:3514–3535):
- D1 (3515–3516) direction loop = continuous `T : ℝ/ℤ → S¹` (unit circle of the oriented plane).
- D2 (3516–3518) tangent-angle lift at a seam = continuous `θ : [0,1] → ℝ`, `T(s) = (cos θ(s), sin θ(s))`, `0 ≤ s ≤ 1`.
- D3 (3519–3521) `tw(T) = (θ(1) − θ(0)) / 2π`.
- D4 (3522–3527) closed C¹ regular oriented curve `γ : ℝ/ℤ → ℝ²`, `γ' ≠ 0`; `T_γ = γ'/|γ'|`; `rot(γ) = tw(T_γ)`.
- D5 (3528–3529) polygon in the regular locus: `rot` stays that of lem:rot. D6 (3529–3530) `R(L) = |rot(L)|` for either.
- D7 (3530–3535) forward reference: "the lemma that follows constructs the lift and proves that these values
  do not depend on its choice, on the seam, or on an orientation-preserving regular reparametrisation";
  transcription note "from CV def:rot ... F-25-88".

CV def:rot paragraph (reference/R/CV/d1_setup.tex:767–787): D1–D4, D6, D7 verbatim (769–785; `T_γ` at 778,
`R(L)` at 785). Differences: CV has no D5 sentence (its polygon `rot` is the ε_i ray formula of the same
definition, 726–765) and no transcription note. Otherwise identical.

SM cf:lem-turnlift (3542–3578; proof 3579–3642) vs CV lem:turnlift (789–822; proof 823–905):
- Preamble: SM 3543–3545 "rot is as in Lemma lem:rot for polygons and Definition cf:def-turning for
  direction loops and closed C¹ regular curves"; CV 790 "rot is as in Definition def:rot".
- (i) SM 3547–3552 = CV 792–797 verbatim: (i-a) every continuous direction loop has a tangent-angle lift;
  (i-b) "the integer tw(T)" is independent of the lift and seam; (i-c) unchanged by orientation-preserving
  reparametrisation; (i-d) constant under a continuous homotopy through direction loops; (i-e) rotation of a
  closed C¹ regular curve is regular-homotopy invariant; (i-f) orientation reversal negates it.
- (ii) SM 3553–3560 (turns `ϑ_i`) = CV 798–805 (turns `τ_i`), same text. DONE (CV.turnlift_ii). SM's proof
  (3621–3624) just cites lem:rot; CV's proof (865–887) is the ray-angle argument that CV/Rotation.lean renders.
- (iii) SM 3561–3575 = CV 806–820 verbatim: (iii-a) rounding: a closed C¹ regular curve obtained from L by
  replacing every corner by a regular arc whose compatible tangent-angle lift has increment ϑ_i has rotation
  rot(L); (iii-b) replacement: arcs b, c with the same endpoints and oriented tangent rays, F_b, F_c closed C¹
  regular, compatible lifts with equal initial values, increments Δ_b, Δ_c: `rot(F_c) − rot(F_b) = (Δ_c − Δ_b)/2π`;
  (iii-c) a continuous path `A_t` in GL⁺(2,ℝ), `A_0 = I`, `A_1 = A`: applying A to both arcs leaves Δ_c − Δ_b unchanged.
- Proof of (i) (SM 3580–3620 = CV 824–864): elementary atan2 subdivision lift "without a covering-space
  theorem"; extension `θ(s+n) = θ(s) + 2πnk` for seam independence; increasing representative
  `φ : ℝ → ℝ`, `φ(s+1) = φ(s)+1` for reparametrisation; local relative angle α(s,t) for homotopies;
  reversed curve `−T_γ(1−s)` has lift `θ(1−s)+π`. Proof of (iii) (SM 3625–3641 = CV 889–905): concatenate
  lifts; complementary lift shared; the loop "c then b backwards" has increment Δ_c − Δ_b and `ν_t(z) = A_t z/|A_t z|`
  is a homotopy, so (i-d) applies "without invoking degree".

## 2. What the Mathlib pin offers (all verified; paths under work/lean/.lake/packages/mathlib/Mathlib/)

Covering maps and lifting (Topology/Covering/Basic.lean, Topology/Homotopy/Lifting.lean):
- `IsCoveringMap (f : E → X) : Prop` (Basic.lean:288); `IsCoveringMap.isLocalHomeomorph` (340), `.continuous` (337).
- `IsCoveringMap.eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂) (he : f ∘ g₁ = f ∘ g₂) (a) (ha : g₁ a = g₂ a) : g₁ = g₂` (368) — uniqueness of lifts.
- `IsCoveringMap.const_of_comp [PreconnectedSpace A] (cont : Continuous g) (he : ∀ a a', f (g a) = f (g a')) (a a') : g a = g a'` (372) — a continuous map into E whose projection is constant is constant. THE workhorse: gives lift uniqueness up to a constant, seam independence, homotopy invariance in 3–6 lines each (prototypes compiled).
- `IsCoveringMap.constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s) (he : ∀ a ∈ s, ∀ a' ∈ s, f (g a) = f (g a')) (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a'` (380) — same on a set; with `isPreconnected_Icc` handles the PRINTED lifts on [0,1] (ContinuousOn).
- `IsCoveringMap.exists_path_lifts (γ : C(I, X)) (e : E) (γ_0 : γ 0 = p e) : ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e` (Lifting.lean:218); `IsCoveringMap.liftPath` (259), `liftPath_lifts` (261), `liftPath_zero` (262), `eq_liftPath_iff` (265).
- `IsCoveringMap.liftHomotopy (H : C(I × A, X)) (f : C(A, E)) (H_0 : ∀ a, H (0, a) = p (f a)) : C(I × A, E)` (Lifting.lean:~300), `liftHomotopy_lifts` (307), `liftHomotopy_zero` (310); `monodromy_theorem` (154); `liftPath_apply_one_eq_of_homotopicRel` (368).
- `IsCoveringMap.existsUnique_continuousMap_lifts [SimplyConnectedSpace A] [LocallyPathConnectedSpace A] (f : C(A, X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) : ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f` (Lifting.lean:468). Instances found: `SimplyConnectedSpace ℝ` and `(ℝ × ℝ)` via `SimplyConnectedSpace.ofContractible` + `RealTopologicalVectorSpace.contractibleSpace` (needs `import Mathlib.Analysis.Convex.Contractible`, `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`); `LocallyPathConnectedSpace ℝ` via `LocallyConvexSpace.toLocallyPathConnectedSpace` (needs `import Mathlib.Analysis.LocallyConvex.Basic`, `Mathlib.Topology.Algebra.Module.LocallyConvex`), products via `Prod.locallyPathConnectedSpace`. So GLOBAL lifts `ℝ → ℝ` and `ℝ × ℝ → ℝ` come for free (no periodic extension needed).
- `IsLocalHomeomorph` (Topology/IsLocalHomeomorph.lean); `isLocalHomeomorph_circleExp` (Analysis/SpecialFunctions/Complex/Circle.lean:457).

Covering targets:
- `Circle.isCoveringMap_exp : IsCoveringMap Circle.exp` (Analysis/SpecialFunctions/Complex/Circle.lean:455), where `Circle.exp : C(ℝ, Circle)` (Analysis/Complex/Circle.lean:118), `Circle.coe_exp : (exp t : ℂ) = Complex.exp (t * I)` (124), `Circle.exp_zero`, `exp_add`, `exp_sub` (143), `exp_neg`, `Circle.exp_eq_exp : exp x = exp y ↔ ∃ m : ℤ, x = y + m * (2π)` (Complex/Circle.lean:74), `exp_eq_one` (90), `periodic_exp` (80), `surjOn_exp_neg_pi_pi` (71), `argPartialEquiv` (51), `injective_arg` (30). `Circle := Submonoid.unitSphere ℂ` (Analysis/Complex/Circle.lean:52), membership = `mem_sphere_zero_iff_norm`.
- `AddCircle.isCoveringMap_coe (p) : IsCoveringMap ((↑) : 𝕜 → AddCircle p)` (Topology/Covering/AddCircle.lean:32; instance `DiscreteTopology (zmultiples (1:ℝ))` found); `AddCircle.homeomorphCircle (hT : T ≠ 0) : AddCircle T ≃ₜ Circle` (Complex/Circle.lean:~437), `AddCircle.toCircle`, `AddCircle.equivIco` (Topology/Instances/AddCircle/Defs.lean:303), `liftIco` (313), `Function.Periodic.lift` (Algebra/Ring/Periodic.lean:217).
- `Complex.isCoveringMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨exp z, _⟩ : {z // z ≠ 0})` (Analysis/Complex/CoveringMap.lean:41), `isCoveringMapOn_exp` (44) — covers the "non-normalized" tangent (nonzero vectors) directly if wanted.
- `Complex.continuousAt_arg (h : x ∈ slitPlane) : ContinuousAt arg x` (Analysis/SpecialFunctions/Complex/Arg.lean:579), `continuousAt_arg_coe_angle (h : x ≠ 0)` (638); `Real.Angle.angle_eq_iff_two_pi_dvd_sub` (Trigonometric/Angle.lean:98), `Real.Angle.toReal_coe` (432), `Real.Angle.continuous_coe` (47); `Real.cos_eq_cos_iff` (Trigonometric/Complex.lean:308, needs that import); `Real.cos_add_pi`, `Real.sin_add_pi` (Trigonometric/Basic.lean:316, 233); `Complex.exp_mul_I`.
- Homotopies: `ContinuousMap.Homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y)` (Topology/Homotopy/Basic.lean:77), `HomotopyRel` (540), `Path.Homotopic` (Homotopy/Path.lean:241). Constancy: `IsPreconnected.constant` / `PreconnectedSpace.constant` (Connected/TotallyDisconnected.lean:328, 334), `IsPreconnected.constant_of_mapsTo` (340) — not needed given `const_of_comp`.
- Winding / turning number / degree of circle maps: NONE in the pin (grep "winding", "windingNumber", "turningNumber", "def degree" in Topology, AlgebraicTopology, Analysis/Complex: no hits). We define `tw` ourselves.

Applicability to our types: `Plane = ℝ × ℝ` (SM/Polygon.lean:13); `SM.planeComplex : Plane → ℂ` (SM/EuclideanPlane.lean:9), `SM.euclideanLength u = ‖planeComplex u‖` (27), `SM.continuous_planeComplex` (SM/RotationContinuity.lean:12), `planeComplex_injective`, `planeComplex_smul`, `euclideanLength_pos`. Bridge (compiled): `def toCircle (u : Plane) (hu : euclideanLength u = 1) : Circle := ⟨planeComplex u, mem_sphere_zero_iff_norm.mpr hu⟩`, `Continuous.subtype_mk (continuous_planeComplex.comp hT) _`, and `((Circle.exp θ : Circle) : ℂ) = planeComplex (Real.cos θ, Real.sin θ)` by `rw [Circle.coe_exp]; apply Complex.ext <;> simp [planeComplex]`; back-conversion by `planeComplex_injective`. So a `Plane`-valued unit loop is a `C(ℝ, Circle)` and Mathlib's lifting through `Circle.exp` applies verbatim; `AddCircle`/`UnitAddCircle` is not needed (we keep `ℝ → Plane` periodic, as the SM library keeps `ℝ`-parametrised things).

## 3. Lean design (module SM/TurningNumber.lean for row 95; SM/TurnLift.lean for row 96)

Imports: `Mathlib.Topology.Homotopy.Lifting`, `Mathlib.Analysis.SpecialFunctions.Complex.Circle`,
`Mathlib.Analysis.Convex.Contractible`, `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`,
`Mathlib.Analysis.LocallyConvex.Basic`, `Mathlib.Topology.Algebra.Module.LocallyConvex`,
`Mathlib.Analysis.Calculus.Deriv.Comp`, `.Deriv.Add`, plus `SM.RotationContinuity`, `SM.RotationTheorem`.

Definitions (row 95, in dependency order):
```lean
structure DirectionLoop where            -- D1, on the printed domain ℝ/ℤ as 1-periodic maps
  T : ℝ → Plane
  continuous : Continuous T
  periodic : Function.Periodic T 1
  unit : ∀ s, euclideanLength (T s) = 1
def IsLift (T : ℝ → Plane) (θ : ℝ → ℝ) : Prop :=          -- global lift (proof device)
  Continuous θ ∧ ∀ s, T s = (Real.cos (θ s), Real.sin (θ s))
def IsSeamLift (T : ℝ → Plane) (θ : ℝ → ℝ) : Prop :=      -- D2 verbatim: [0,1] only
  ContinuousOn θ (Set.Icc 0 1) ∧ ∀ s ∈ Set.Icc (0:ℝ) 1, T s = (Real.cos (θ s), Real.sin (θ s))
theorem exists_lift (L : DirectionLoop) : ∃ θ, IsLift L.T θ    -- (i-a); ~25 lines, see below
noncomputable def lift (L) : ℝ → ℝ := Classical.choose (exists_lift L)
theorem lift_isLift (L) : IsLift L.T (lift L) ∧ IsSeamLift L.T (lift L)
noncomputable def tw (L : DirectionLoop) : ℝ := (lift L 1 - lift L 0) / (2 * Real.pi)   -- D3
structure ClosedC1Curve where            -- D4: γ' ≠ 0 everywhere, 1-periodic, C¹
  γ γ' : ℝ → Plane
  hasDerivAt : ∀ t, HasDerivAt γ (γ' t) t
  continuous_deriv : Continuous γ'
  regular : ∀ t, γ' t ≠ 0
  periodic : Function.Periodic γ 1
theorem ClosedC1Curve.deriv_periodic (c) : Function.Periodic c.γ' 1   -- compiled (HasDerivAt.scomp + .unique)
noncomputable def ClosedC1Curve.tangentLoop (c) : DirectionLoop :=     -- T_γ = γ'/|γ'|
  ⟨fun t => (euclideanLength (c.γ' t))⁻¹ • c.γ' t, …, …, …⟩             -- continuity/unit compiled
noncomputable def ClosedC1Curve.rot (c) : ℝ := tw c.tangentLoop           -- D4
noncomputable def ClosedC1Curve.R (c) : ℝ := |c.rot|                      -- D6 (polygons: |rotationNumber L|, D5)
```
`tw` is ℝ-valued with an integrality theorem, like `SM.rotationNumber`; `CV.rot : ℤ` connects by cast
(`CV.rot_eq_rotationNumber`). D5 needs no new object: `SM.rotationNumber` is cited. The printed lift domain
[0,1] is kept as `IsSeamLift`; `tw` is computed from the global `lift`, which restricts to a seam lift, and
(i-b) proves every seam lift gives the same value — so the definition is an instance of the printed one.
Dependency order: `exists_lift` (a clause of the LEMMA) must be proved before `tw` can be defined; the
printed definition itself acknowledges this (D7). Put the theorem in the definition module and re-export it
in the lemma's data structure. No junk-value fallback.

Proof routes (all prototyped in /tmp/scout3–5.lean, compiled):
- (i-a) existence: `Tc : C(ℝ, Circle) := ⟨fun s => toCircle (L.T s) (L.unit s), …⟩`; pick `θ₀` with
  `Circle.exp θ₀ = Tc 0` (`Circle.surjOn_exp_neg_pi_pi`); `Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts Tc 0 θ₀ _`
  gives `F : C(ℝ, ℝ)` with `Circle.exp ∘ F = Tc`; convert pointwise with the cos/sin bridge. (The printed
  atan2 subdivision is not needed; the checked object is the statement. Note it in the docstring.)
- (i-b) lift independence: for lifts θ₁, θ₂, `const_of_comp` on `g s := θ₁ s − θ₂ s` (exp g = 1) ⇒ θ₁ − θ₂ constant
  ⇒ equal increments; seam-lift version via `constOn_of_comp isPreconnected_Icc`. Integrality: `Circle.exp (θ 1) = Circle.exp (θ 0)`
  by periodicity, `Circle.exp_eq_exp` ⇒ `θ 1 − θ 0 = m·2π`. Seam independence: `const_of_comp` on `s ↦ θ(s+1) − θ s`
  ⇒ `θ (a+1) − θ a = θ 1 − θ 0` for every seam a; also `tw (L.shift a) = tw L`.
- (i-c) reparametrisation: `φ : ℝ → ℝ` continuous, monotone, `φ (s+1) = φ s + 1` (printed representative);
  `θ ∘ φ` lifts `T ∘ φ`; increment `θ (φ 0 + 1) − θ (φ 0)` = `θ 1 − θ 0` by seam independence.
- (i-d) homotopy: `H : ℝ × ℝ → Plane` continuous, `∀ t, DirectionLoop (H · t)`; lift `H` globally on `ℝ × ℝ`
  (`existsUnique_continuousMap_lifts`, instances verified) to `Θ`; `g t := Θ (1,t) − Θ (0,t)` continuous with
  `Circle.exp (g t) = 1` ⇒ constant (`const_of_comp` on ℝ); `Θ (·, t)` lifts `H (·, t)` ⇒ `tw (H·t) = g t / 2π`.
  The printed `0 ≤ t ≤ 1` version: extend by `H (s, projIcc 0 1 t)` (`continuous_projIcc`), or state on ℝ.
  No `liftHomotopy` needed (it is available if a `C(I × A, ·)` formulation is preferred).
- (i-e) regular homotopy: `Γ Γ' : ℝ × ℝ → Plane`, `∀ s t, HasDerivAt (Γ · t) (Γ' (s,t)) s`, `Continuous Γ'`,
  `Γ' ≠ 0`, periodic in s ⇒ normalised `Γ'` is a homotopy of direction loops ⇒ (i-d) gives `rot Γ₀ = rot Γ₁`.
- (i-f) reversal: `reverse c := ⟨fun s => c.γ (1 − s), fun s => −c.γ' (1 − s), …⟩` (chain rule
  `(hd (1−t)).scomp t ((hasDerivAt_id' t).const_sub 1)`, compiled); lift `s ↦ θ (1 − s) + π` using
  `Real.cos_add_pi`, `Real.sin_add_pi` (compiled) ⇒ `rot (reverse c) = − rot c`.
- (iii) needs increments of direction PATHS (unit-vector `u : ℝ → Plane`, continuous, no periodicity):
  `incr u a b := θ b − θ a` for any lift (exists by the same theorem with `existsUnique_continuousMap_lifts`, is
  well defined by `const_of_comp`); lemmas: additivity `incr u a c = incr u a b + incr u b c`, constant piece ⇒ 0,
  affine reparametrisation, reversal `incr (fun s => −u (1−s)) = −incr u`, and `2π · tw L = incr L.T 0 1`.
  (iii-a) rounding, direction-level reading of "obtained from L by replacing every corner by a regular arc":
  breakpoints `p : Fin (2c+1) → ℝ`, `p 0 = 0`, `p (2c) = 1`, monotone; on `[p(2i), p(2i+1)]` `T_γ` is constant
  `= edge L i / |edge L i|`; on `[p(2i+1), p(2i+2)]` (corner at `q_{i+1}`) `incr T_γ … = principalTurn L (i+1)`
  ("compatible lift has increment ϑ"). Then `2π rot γ = Σ principalTurn L i = 2π rotationNumber L` — by the
  DEFINITION `rotationNumber P = (Σ principalTurn P i)/(2π)` (SM/RotationNumber.lean:10); `turnlift_ii` is
  not needed. This is the only place polygons meet direction loops; cf:def-turning itself (D5) only cites lem:rot.
  (iii-b) replacement: loops `T_b`, `T_c` with `λ, μ ∈ (0,1)`, `T_b` on `[0,λ]` ≙ arc b, `T_c` on `[0,μ]` ≙ arc c
  (`incr = Δ_b, Δ_c`), and `T_b|[λ,1]`, `T_c|[μ,1]` affine reparametrisations of one complementary path
  ⇒ `rot F_c − rot F_b = (Δ_c − Δ_b)/2π` by additivity + reparametrisation. (iii-c) GL⁺: `A : ℝ → (Plane →ₗ[ℝ] Plane)`
  (or four continuous real entries) continuous with `det ≠ 0` and `A 0 = id`; arcs as nonzero tangent paths
  `b c : ℝ → Plane` with `b 0 ∥⁺ c 0`, `b 1 ∥⁺ c 1`; the loop "normalise c, then normalise b backwards" has
  `2π tw = Δ_c − Δ_b` (additivity + reversal); `(s,t) ↦ normalise (A t (loop s))` is a homotopy of direction
  loops (continuity of normalisation compiled) ⇒ (i-d) ⇒ increments equal at t = 0 and t = 1.

## 4. Effort, risks, partition

| lemma / definition | est. lines |
|---|---|
| Plane↔Circle bridge (`toCircle`, cos/sin identity, continuity, back-conversion) | 40 |
| `DirectionLoop`, `IsLift`, `IsSeamLift`, `exists_lift`, `lift`, `tw`, `tw_int` | 90 |
| `ClosedC1Curve`, `deriv_periodic`, `tangentLoop` (continuity, unit, periodic), `rot`, `R`, row-95 data bundle | 110 |
| (i-b) lift/seam independence (global + printed [0,1] lifts), `tw_shift` | 70 |
| (i-c) reparametrisation | 40 |
| (i-d) homotopy through direction loops (ℝ×ℝ lift, projIcc version) | 70 |
| (i-e) regular homotopy structure + `rot` invariance | 70 |
| (i-f) reversal (`reverse`, chain rule, lift `θ(1−s)+π`) | 60 |
| direction-path increments: existence, well-definedness, additivity, constant, affine reparam, reversal | 150 |
| (iii-a) rounding (breakpoint model, telescoping sum over `Fin (2c)`, `= rotationNumber`) | 120 |
| (iii-b) replacement identity | 70 |
| (iii-c) GL⁺ path model, concatenated loop, homotopy `ν_t`, conclusion | 130 |
| row-96 `TurnliftData` bundle (i)+(ii re-export)+(iii); CV rows 144/145 re-exports (`CV.tw := SM.tw` etc., cast to `CV.rot`) | 80 |
| total | ~1100 (range 950–1300) |

Riskiest points: (1) the STATEMENT models for (iii): "obtained from L by replacing every corner", "compatible
lifts", "regular oriented arcs", "path in GL⁺(2,ℝ)" have no printed formal definitions; the direction-level
readings above follow the printed proof (3625–3641) exactly but must be documented per clause, as
CV/Rotation.lean does — reviewer pushback is likeliest here. (2) Telescoping over `Fin (2c)` breakpoints against
`ZMod c` indices of `principalTurn` (index bookkeeping; `Fin.sum_univ_succ`/`Finset.sum_range_succ` on the
cast). (3) `HasDerivAt` on `Plane = ℝ × ℝ` uses the product norm while `T_γ` uses `euclideanLength`; fine
(normalisation continuity compiled) but keep `euclideanLength`, never `‖·‖`. (4) Import weight: the lifting
file pulls FundamentalGroupoid/SimplyConnected; load measured at ~5 s, acceptable. (5) The homotopy clause's
parameter domain ([0,1] printed vs ℝ): state the printed version and derive it from the ℝ version by projIcc.
(6) Proof method differs from the printed elementary one (covering-space theorem instead of atan2
subdivision) — statement-faithful; record in the module header.

Proposed prover units (each a `lake env lean`-checked draft, standard axioms):
- U1 (row 95, definitions + `exists_lift` + `tw_int` + bridge): ~240 lines. Start now.
- U2 (row 96 (i-b,c,d): independence, seam, reparametrisation, homotopy): ~180 lines. After U1.
- U3 (row 96 (i-e,f): regular homotopy, reversal; (i) bundle): ~130 lines. After U1 (parallel to U2).
- U4 (row 96 (iii): path increments, rounding, replacement, GL⁺): ~470 lines. After U2 (uses (i-d)).
- U5 (row 96 data bundle with (ii) re-export; CV rows 144/145 re-exports and `RotDefinitionData` extension): ~80 lines. After U3, U4.

Prototype files (kept for the provers): /tmp/scout3.lean (lift existence, uniqueness, seam, integrality,
[0,1]-lift, ℝ×ℝ lift), /tmp/scout4.lean (Plane↔Circle bridge, normalisation, cos/sin+π), /tmp/scout5.lean
(derivative periodicity, reversal chain rule). Nothing was written under work/lean.
