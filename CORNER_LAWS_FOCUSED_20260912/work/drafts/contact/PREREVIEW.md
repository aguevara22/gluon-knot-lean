# PREREVIEW — contact lane (`SM.src_contact`, `SM.sl`, rows 94 / 161 / 162)

Independent auditor, 2026-09-15 (pre-review of the frozen statements `work/drafts/contact/Skeleton_FINAL.lean`,
ported verbatim to `work/lean/SM/SrcContact.lean`, `SM/FdContactStatements.lean`, `CV/AxEtnyre.lean`; the
diff of the port against the draft is header text only).  This is NOT the formal interface review; it answers
four questions: (1) non-vacuity and truth of the axiom, with an independent numeric probe; (2) truth of the
11 unit theorems `u_*` of §5.4; (3) fidelity red flags on `FdContactData`, `CV.AxEtnyreData`,
`CV.AxSlboundData` beyond FR-SC-1..11 / FR-FC-1..7; (4) triviality.

Registry text read: sm-3:3341-3365 (src:contact), 3404-3492 (fd:contact + proof), 3012-3022
(rem:sl-convention), 3328-3340 (def:transverse-front), 2395-2409 and 2480-2505 (row 84 and its annulus),
2810-2826 (fd:framed-linking); d10_axioms.tex:387-425 (CV 161/162); d3_floor.tex:926-990 (the consumer
thm:carrierfloor (C)); Etnyre §2.2 (3) "positive y axis goes into the page", §2.6.2 (5)/(7), §2.6.4 (9),
§2.9 Fig. 23-24, Warning, Lemma 2.22 (17) (SOURCES/audit/L-3_EXIT/work/etnyre_p4-20.txt:160-172, 445-525,
675-730).  Accepted Lean read: `linking`/`gaussMap`/`gaussDensity`/`lcCrossingSign`/`selfLinking`/
`IsPositiveTransverseEmbedding`/`TransverseFamily`/`LinkingCalculusDataOf` (SM/LinkingCalculus.lean
361-640), `SmoothKnotDiagram`/`TransverseKnot`/`front` (SM/TransverseFront.lean), `SmoothFront` with
`cuspDisc`/`IsDownCusp`/`slope`/`IsOverUnder`/`crossSign`/`Marking`/`GeomRounding`/`Rounding`
(SM/FrontSmooth.lean), rows 84/87 statements (TransverseNeighborhood.lean 40-215, GenericFront.lean 40-225),
rows 89-91 vocabulary (CeSmoothingRecord.lean 141-335, ContactPathOfDescent.lean 149-160, ContactPath.lean),
row 93 (NgBound.lean 64-106), the sweep block (`U8R.recordIso`, `sweep_proof`, `frontRecord`,
`realizeRecordIso`, `Diagram.record`, `visitBetween_iff_of_nextVisit_comm`).

Compile check (`lake env lean` on a copy of Skeleton_FINAL.lean with `#print axioms` appended; 10 s):
`fd_contact_of_units` depends on {propext, Classical.choice, Quot.sound, lit_homfly, lit_homfly_descent,
lp_lm, lp_lm_uniqueness, ng_finite_word, src_contact}; `src_contact_iff_consequence` standard only;
`CV.ax_etnyre` standard + `src_contact`; `U_package_of` standard only; rows 84, 87, 88, 89, 92 standard
only; row 91 = lit_homfly + lit_homfly_descent + lp_lm + lp_lm_uniqueness; row 93 = lp_lm + ng_finite_word.
All as claimed in PLAN_FINAL §0.

## 1. Non-vacuity and truth of the axiom

### 1.1 Satisfiability

`SrcContactClauses r tb` is satisfiable iff `SrcContactConsequence` holds (`src_contact_iff_consequence`,
standard axioms only — verified by compile).  So the axiom asserts exactly:

* (P) for every `L`, `F` with `IsLegendrianFrontOf L F` and every `T'` with
  `GenericFront.IsPositivePushoff L T'`: `slCircle T' = F.writhe − F.downCount`;
* (T) for every `K : TransverseKnot`: `slCircle K.circle = K.front.writhe`.

Neither clause asserts existence of anything, so the axiom is non-vacuous only in the sense that it has
content on a non-empty class: the class of (P) is non-empty (the Legendrian "eye" below has a front on
ng:front-domain and an accepted-shape annulus; checked analytically: cusps semicubical with
`det(γ″,γ‴) = ∓2·(2π)⁵ ≠ 0`, `x″ ≠ 0`, no double points), and the class of (T) is non-empty (the transverse
unknots below).  `slCircle` is applied only on its domain: a circle `B(·,s₀)` of an accepted annulus is a
2π-periodic positive transverse embedding (smooth as a slice of `ContDiffOn` on the OPEN strip, injective mod
2π from `injective` at `s = s' = s₀`, positive from `positive`), and `K.circle` is one by U0 — so the
`else 0` branch of `slCircle` is never what the clauses constrain (if it were, (P) would force `w − D = 0`,
a falsity; it is not).

### 1.2 Truth on the accepted definitions (mathematics)

Chain of identifications, each checked against the accepted Lean text and Etnyre's text:

1. **Gauss normalization.** `linking P C₁ C₂ = (1/4π)∫∫ G·(G_u × G_v)`, `G = (C₂(v) − C₁(u))/|…|`, with
   Mathlib's right-handed `crossProduct`.  Dropping the components of `G_u`, `G_v` along `G`,
   `G·(G_u × G_v) = (C₂(v) − C₁(u))·(C₂′(v) × C₁′(u))/|C₂(v) − C₁(u)|³`, the classical Gauss integrand
   with the standard sign.  Probe: a Hopf link whose second component pierces the first's spanning disc
   against its normal gives `−1.0000` (both a literal finite-difference implementation of `G·(G_u × G_v)`
   and the closed form), and the crossing formula with `ν = −∂_y` in the accepted `lcCrossingSign`
   convention gives `−1` by hand.  So `linking` is the standard linking number.
2. **The section.** `∂_y ∈ ker(dz − y dx)` everywhere (`α(∂_y) = 0`), so `ℓ(T, T + ε∂_y)` is the
   self-linking number for the trivialization of `ξ_std` by `∂_y` — exactly Etnyre §2.6.4 ("`v = ∂/∂y` is
   always in `ξ_std`") and rem:sl-convention.  Independence of the section is Geiges; Etnyre's `sl` IS this
   number.
3. **Transverse clause (T).** `ℓ(T, T + ε∂_y)` equals the linking with the blackboard pushoff of the
   `xz`-projection (the framing `cos τ ∂_y + sin τ n`, `n` the in-plane normal, never meets `ℝT′` since
   `(x′,z′) ≠ 0`), i.e. the writhe of the projection with the nearer strand over.  Observer at `y = −∞`
   (`ν = −∂_y`, `det(e_x, e_z, −e_y) = +1`): nearer = smaller `y` = row 92's `IsOver`, sign
   `sgn det_xz(u_O, u_U)` = row 92's `crossSign` = the standard right-handed sign (the front block's
   standard crossing `(1,−1),(1,1)` has `det = 2 > 0` and is right-handed for this observer).  Etnyre (9)
   with "the positive y axis goes into the page" is the same observer.  TRUE.
4. **Pushoff clause (P): `T₊(L)` on the accepted vocabulary.** An accepted `IsPushoffAnnulus` has
   `α(∂_θ B) = 0` at `s = 0`, so its `transverse` field forces `α(∂_s B)|_{s=0} ≠ 0`: the annulus is
   genuinely tilted out of `ξ` along `L` (not the Legendrian ribbon).  For small `s` the circle `B(·,s)` is
   `C¹`-close to `L` (smooth on the open strip, periodic), hence a section of the standard neighbourhood
   `J¹(S¹) ⊃ L` (coordinates `(θ,x,y)`, `α = dy − x dθ`); positive transverse sections `(x(θ), y(θ))` are
   those with `y′ − x > 0`, a CONVEX condition, so any two are transversely isotopic through positive
   transverse sections — including Etnyre's model `L₊ = {x = −s, y = 0}` (Fig. 23; "any two transversal
   push-offs are transversely isotopic").  Circles with larger `s₀ < b` are isotopic to small ones through
   the annulus itself (all slices positive transverse embedded, jointly smooth).  Reparametrisation is
   absorbed by `TransverselyIsotopic`'s `ρ`.  Hence every `IsPositivePushoff L T'` is Etnyre's `T₊(L)` up
   to transverse isotopy, and `slCircle` is an isotopy invariant (row 88).  Note the sign of `α(∂_s B)`
   does NOT matter (both tilts are `L₊`; probe below confirms).
5. **`D`, `U`, `w` conventions.** Etnyre (5): `r = (D − U)/2`, `D` = down cusps, "positive when going down
   a cusp"; (7): `tb = w − (#cusps)/2`; (17): `sl(T₊) = tb − r = w − D`.  Row 73's `IsDownCusp`
   (`x″·det(γ″,γ‴) < 0`) is "traversed from the locally upper arm to the lower" (FR-2, checked on the
   germ `(Au², ⅔Au³)`: `cuspDisc = 16A³`, later arm higher iff `A > 0`); for a Legendrian front
   `det(γ″,γ‴) = 2x″²y′` at a cusp, so `cuspDisc = 2x″³y′` and down ⇔ `x″y′ < 0`, the geometric reading.
   `w` = over-first `det_xz` sign with over = smaller slope = smaller `y` (`y = dz/dx` on a Legendrian),
   Etnyre (3).  Etnyre's Warning (Bennequin reverses `±`) is exactly what the probe decides: the
   accepted-shape annuli give `w − D`, never `w − U` (case with `D = 1`, `U = 3` below).

Conclusion: (P) and (T) are TRUE on the accepted definitions with the accepted sign conventions; the axiom
is satisfiable and its unique-up-to-`r`,`tb` content is true mathematics.

### 1.3 Independent numeric probe (python, numpy; scripts and outputs in `work/drafts/contact/prereview_probe/`)

Written from the accepted definitions, not from `probe_judge.py`: the integrand implemented two ways
(finite differences of `G`; the closed form), periodic midpoint rule on an `N×N` grid; front double points by
segment intersection on the `xz` projection with the accepted over rules; cusps by the accepted `cuspDisc`
(dedup mod 2π); embeddedness by min distance over pairs with parameter separation `> 0.3·2π`.

| object | class check | front writhe (accepted rule) | `D`,`U`,`w` of the Legendrian | Gauss `sl` | expected |
|---|---|---|---|---|---|
| Hopf link `(cos,sin,0)`, `(1+cos,0,sin)` | — | hand crossing formula `−1` | — | `−1.0000` (both implementations, `N = 600–800`) | `−1` |
| `T₁ = (cos t, sin t, sin 2t/4)` | `α = ½` | `−1` (one crossing, over `y = −1`) | — | `−1.0000` at `ε = 0.05, 0.1`, `N = 1000, 2000, 4000`, both implementations | `−1` |
| `T₂ = (−sin t, 2cos t, −sin t cos t)` | `α = 1` | `−1` | — | `−1.0000` (`ε = 0.05, 0.1`) | `−1` |
| `T₃ = (2cos t + cos 2t, −4x′, sin 6t/6 + 0.2 sin 3t + 0.3 cos t + 0.25 sin t)` | `α ≥ 0.129`, 5 crossings, y-gaps `≥ 2.74` | `−3` | — | `−3.0001` (`ε = 0.2`, `N = 16000`); `−3.019` (`ε = 0.1`, `N = 16000`, converging) | `−3` |
| Legendrian eye `L = (cos t, −sin 2t/2, sin³t/3)`; annulus `B = L + s(e_z − x′e_y) + s²(sin 2t/2)e_z` (`α(∂_sB)|₀ = +1`, `α(∂_tB_s) = s x′² + s² cos 2t` exactly) | `α(L′) = 0` to 1e-16; circle `B(·,0.3)`: `α ≥ 0.09`, embedded | circle: `−1` — ONE kink crossing at the DOWN cusp `t ≈ π`, sign `−1` | `D = 1, U = 1, w = 0`; `tb − r = −1` | `−1.00000` (`s₀ = 0.3`, `ε = 0.05, 0.1`, `N = 4000, 6000`); `−0.9957` (`s₀ = 0.1`, `ε = 0.05`, `N = 3000`) | `w − D = −1` (`= w − U` here) |
| same eye, annulus with `V = −e_z − x′e_y` (`α(∂_sB)|₀ = −1`) | same | circle: `−1`, same kink | same | `−0.9998` (`s₀ = 0.3`, `ε = 0.05`, `N = 3000`) | `−1` (tilt sign irrelevant, §1.2.4) |
| `L₄`: `x = cos 2t + cos t`, `y = sin t − sin 2t/2 + 0.3 sin 3t`, `z′ = x′y` (exact trig poly); annulus `B = L₄ + s(0, −x′, 1) + s²(sin 4t/4)e_z` | `α(L₄′) = 0` to 3e-15, `|L₄′| ≥ 0.9`, embedded (self-approach 0.68); circle `B(·,0.2)`: `α ≥ 0.0195`, self-approach 0.74 | circle: `−1` — one kink at the down cusp `t ≈ 0`, sign `−1` | **`D = 1, U = 3, w = 0`**; `r = −1`, `tb = −2`, `tb − r = w − D = −1`; `w − U = −3` | **`−1.0000`** (`s₀ = 0.2`, `ε = 0.1`, `N = 16000`; `−1.0014` at `N = 8000`) | `w − D = −1`, NOT `w − U = −3` |
| crossing Legendrian `a = 2.4, γ = −0.8` (same family), annulus `W = sin 6t/6` | embedded; circle `B(·,0.25)`: `α ≥ 0.008`, max speed 6.1 | `L`: 3 crossings, `w = 1`; circle: 5 crossings (3 inherited + 2 kinks at the 2 down cusps), writhe `−1` | `D = 2, U = 2, w = 1`; `tb − r = −1` | `−1.020` (`ε = 0.05`), `−1.008` (`ε = 0.08`) at `N = 20000` (from `−1.26`, `−0.92` at `N = 12000`: converging) | `−1` |

Reading of the numbers: (a) the accepted `linking` is the standard Gauss linking number (Hopf `−1` by
three routes); (b) the transverse clause holds to 4-5 digits on unknots and on a 5-crossing positive
transverse curve; (c) the pushoff clause holds to 4-5 digits on the eye, and the `L₄` case with `D ≠ U`
decides Etnyre's Warning in the direction the axiom takes: `sl(T₊) = w − D` (`−1`), not `w − U` (`−3`) —
so `IsPositivePushoff` is Etnyre's positive pushoff and row 93's `slNg = w − D` is the right quantity;
(d) the tilt sign of the annulus is irrelevant, as §1.2.4 predicts; (e) the mechanism claimed in
PLAN_FINAL §4 (one kink per DOWN cusp, sign `−1`, none at up cusps) is reproduced on three different fronts
(1, 1, 2 down cusps → 1, 1, 2 kinks).  Discretisation note: the Gauss grid must resolve the peak of width
`ε/|T′|` near the diagonal AND the pushoff must not pass through the kink loop (`ε ≲ s₀/3`); the judge's
`−0.9998` and my `−1.00000` are the same converged value.

**Verdict on (1): the axiom is satisfiable, non-vacuous and TRUE on the accepted definitions with the
accepted conventions.  The judge's probe is confirmed and extended (a `D ≠ U` case; a multi-crossing
transverse curve; both annulus tilts).**

## 2. Truth probes of the 11 unit theorems (`Skeleton_FINAL.lean` §5.4)

All statements are frozen; I judge truth on the accepted definitions, not proof effort.

| unit | verdict | reason |
|---|---|---|
| `u_circle : ∀ K, TransverseNeighborhoodHyp K.circle` | TRUE | `K.circle θ = toE3 (K.T (θ/2π))`: smooth (`toE3` linear ∘ smooth ∘ affine); 2π-periodic from 1-periodicity; injective mod 2π from `K.embedded` (`SameT`); immersion and `α > 0` by the chain rule `deriv = (1/2π)·toE3 (deriv K.T)` with `deriv_T_ne_zero`, `positive`. |
| `u_sl_radius` | TRUE | `slCircle T = selfLinking T ε₀` (`ε₀` = chosen radius). Apply row 88 `self_linking_invariant` on the constant family with the radius bound `max ε ε₀` (NOT `min` as PLAN §6 says): radii `≤ ε` are disjoint by the hypothesis, radii `≤ ε₀` by `transverse_uniform`'s `DisjointPair`; then `selfLinking T ε = selfLinking T ε₀`. |
| `u_sl_family` | TRUE | `transverse_uniform` gives `ε₀` for the family; each `F s`, `s ∈ [0,1]`, is a positive transverse embedding (spec), so `slCircle (F s) = selfLinking (F s) ε₀` by U1a; `self_linking_invariant` equates the two ends at radius `ε₀`. |
| `u_sl_reparam` | TRUE | `ρ_s = (1−s)·id + s·ρ`: `ρ_s′ = (1−s) + sρ′ > 0`, `ρ_s(θ+2π) = ρ_s(θ) + 2π`, strictly increasing bijection, so `T∘ρ_s` is a 2π-periodic positive transverse embedding (`α((T∘ρ_s)′) = ρ_s′·α(T′∘ρ_s)`), jointly smooth; U1b at `s = 0, 1`. |
| `u_sl_isotopy` | TRUE | Clock `η = Real.smoothTransition` (`0` on `s ≤ 0`, `1` on `s ≥ 1`): `G s := F (η s)` is a `TransverseFamily (2π)` on `ℝ × ℝ` (`ContDiffOn.comp_contDiff` with values in `Icc 0 1 ×ˢ univ`; slices embedded positive since `η s ∈ [0,1]`); U1b gives `slCircle T₀ = slCircle (T₁∘ρ)`; `T₁` is itself a positive transverse embedding (`= (T₁∘ρ)∘ρ⁻¹`, `ρ⁻¹` a circle reparam), so U1c finishes. |
| `u_legendrianFront` | TRUE | `F := ⟨1, _, fun _ => ⟨front Lc (2π·), …⟩, …⟩`. `γ′ = x′(1, y)` (Legendrian), so `γ′ = 0 ⇔ x′ = 0` = `cuspSet`: `cusps_finite` from `finite_cusps`, `no_vertical` immediate. At a cusp the exact germ (`x = x₀ + Au²`, `z = z₀ + Ay₀u² + ⅔Au³`, `u = y − y₀`, `u′ = y′ ≠ 0`) gives `γ″ = (2Au′², 2Ay₀u′²)`, `γ‴ = (6Au′u″, 6Ay₀u′u″ + 4Au′³)`, `det(γ″,γ‴) = 8A²u′⁵ ≠ 0`, `x″ = 2Au′² ≠ 0` (my independent computation agrees with PLAN §6). `doubles_finite`/`transverse`/`no_triple`/`cusp_alone` are `finite_double`/`transverse_double`/`no_triple`/`no_cusp_on_branch` under `θ = 2πt` (`SameParam` on `Fin 1 × ℝ` ↔ `GenericFront.SameParam`). |
| `u_spatialOf` | TRUE | `sp.T _ t := toSpace (Lc (2πt))`: smooth, 1-periodic, embedded (injectivity mod 2π → `SameT`), regular (immersion). `CuspedProjection`: cusps = `x′ = 0` finite; `ExactCuspGerm` from `IsExactCuspGerm` — same formula (`2/3·A`), middle coordinate literally `y`, and `y′ ≠ 0` on a δ-interval by continuity of `y′` from `y′(θc) ≠ 0`; `heights_distinct` from embeddedness of `Lc` (equal `xz` and equal `y` ⇒ same point ⇒ `SameParam`). |
| `u_reading : ∀ F : SmoothFront, ∃ S, Nonempty (F.Marking S)` | TRUE | Every `SmoothFront` (accepted class, any `c ≥ 1`, cusps allowed, crossing-free circles allowed) has one: `sweep_proof F : SweepStatement F` (accepted, axiom-free) gives a nonempty word `W` with `RecordIso (frontRecord F) (slotRecord …)`, and `U2.realizeRecordIso W h : RecordIso (realize W).diagram.record (slotRecord …)`; compose to `ι : RecordIso (frontRecord F) S.record`, `S := (realize W).diagram`. `Marking.ofRecordIso ι`: `e := ι.e` (`frontRecord.comps = Fin F.c`, `S.record.comps = Fin S.Γ.c`), `Φ := ι.Φ` (`M = F.Occ`, `S.Γ.Visit`), `comp_eq` from `ι.comp_eq` (`occComp p = p.1.1`, `S.record.comp = compOf`), `pair_eq` from `ι.pair_eq` + uniqueness of the partner (`partnerPerm`, `pairPerm = twin`), `over_iff` from `ι.bit_eq` (`frontOver F p = decide (slope p < slope (partner p))`, `S.record.isOver = overBit`), `sgn_eq` from `ι.sgn_eq` (`frontSgn` = over-first `sign det`, `S.record.sgn v = S.sign v.1`), `between_iff` from `ι.succ_eq` (`frontRecord.succ = cycNext` on `occKey p = p.1.2`, `S.record.succ = visitSucc`): on a finite cycle a successor-preserving bijection preserves the strict cyclic betweenness because both successors are the sorted ones (`cycNext_no_between`, `record_succ_no_between`) — the same argument as the accepted Diagram-Diagram lemma `visitBetween_iff_of_nextVisit_comm` (LinkDiagramRecord.lean:1009), which enumerates a component and uses `ent_add_sub`. Mathematically certain; the Lean effort (R1) is real but every ingredient is accepted. |
| `u_transport` | TRUE | (i) `F.IsRounding S := ⟨G, geom, m⟩` with `geom : F.GeomRounding G` transported field-by-field from `sp.CleanCuspSmoothing G` (identical fields `U a b disc center disjoint a_lt lt_b len clean arc_in arc_simple agree inside regular simple no_crossing`; `collar` dropped) along `F.comp 0 .γ = xzOf (sp.T 0)` (given `sp_T` and `IsLegendrianFrontOf.front`; `F.Cusp ≃ sp.cuspSet` since `vel = 0 ⇔ projected velocity = 0`). (ii) `HeightMarking sp G S` from `m : F.Marking S`: `OccOf G ≃ OccOf sp.projLoop` (`CleanCuspSmoothing.occEquiv`, accepted: a clean smoothing keeps the double points) `≃ F.Occ`; `over_iff`: at a double point of a Legendrian front `slope = z′/x′ = y = height` EXACTLY (`x′ ≠ 0`: double points are not cusps, `no_vertical`), so `slope p < slope q ↔ height p < height q` — the printed remark "for a Legendrian front this is also the smaller-slope rule `y = dz/dx`" (sm-3:3430-3431); `sgn_eq`: velocities of `G` and `F` agree at double points (`deriv_eq_of_isDouble`/`crossSignOf_eq`). |
| `u_regular : ∀ K, K.spatial.RegularGenericProjection` | TRUE | `regular` = `K.immersion`; `doubles_finite` = image of `K.doubles_finite` under `fst` (`occSetOf` on `Fin 1 × ℝ`); `transverse`, `no_triple` verbatim from `K`; `heights_distinct` = `y_ne_of_isDouble`. |
| `u_family` | TRUE | `G t := toSpace ∘ Ψ (η t) ∘ Φ (1 − η t) ∘ L ∘ (2π·)` with the clock `η`: joint `C^∞` on `ℝ × ℝ` by two applications of `ContDiffOn.comp_contDiff` into `Icc 0 1 ×ˢ univ`; each slice smooth, 1-periodic, embedded (`Ψ_t`, `Φ_s` are bijections for `t, s ∈ [0,1]` by `diffeo`, `L` injective mod 2π, `toSpace` bijective) and regular (`fderiv` of a map with a smooth two-sided inverse is injective by the chain rule; `L′ ≠ 0`). `G 0 = pkg.sp` (`Ψ 0 = id`, `η 0 = 0`; `SpatialLink` ext on `T` with `pkg.sp_T`); `G 1 = K.spatial` (`Φ 0 = id` from `IsContactIsotopy.ambient.zero`, `Ψ 1 ∘ L = K.circle` = `carries`, `toSpace ∘ toE3 = id`), so `RegularGenericProjection` is U6a and the reading transport is `▸`. Slope-versus-height at double points is NOT needed here (`HeightMarking` is on the transverse end). |

None of the 11 is DOUBTFUL or FALSE.  Effort-only risks: `u_reading` (R1, the cyclic-order transport lemma;
a Diagram-Diagram model proof exists), `u_legendrianFront` (R2, order-3 chain rule for `γ ∘ u`; the linear
case is `germFront_*`), `u_family` (R3, engineering).  One correction to PLAN §6: U1a's common radius must be
`max ε ε₀`, not `min`.

## 3. Fidelity red flags NOT among FR-SC-1..11 / FR-FC-1..7

RF-1 (`FdContactData.over_rule_sign`, non-blocking).  The printed first sentence is a convention for "the
`xz` front page" in general — fd:contact's proof applies it to BOTH the transverse front and the Legendrian
front ("For a Legendrian front this is also the smaller-slope rule `y = dz/dx`").  The field states only the
transverse-class half, where it is definitional on row 92 (`rfl`-level, proved by `fdContact_over_rule_sign`).
The Legendrian half (slope = `y` at double points, i.e. row 73's over rule = the smaller-`y` rule) has no
field; it lives inside unit U5 (`u_transport`).  Suggest one sentence in the module docstring saying so.

RF-2 (`representative_bound`, `AxSlboundData.bound`: reading EXISTENCE, non-blocking but consumer-critical).
Both are universally quantified over readings `X` with `Nonempty (K.spatial.HeightMarking
K.spatial.projLoop X)`; nothing in the package asserts that a regular projection HAS a `HeightMarking`
(`U_reading` is for `SmoothFront`s only, with the slope rule).  The consumer thm:carrierfloor (C)
(d3_floor.tex:966-975) builds a smooth positive transverse lift whose "front and smaller-`y` over/under
assignments are exactly `T`" and then needs `P_T = P_{D̄}` — in Lean it must PRODUCE a `HeightMarking` of
`K.spatial` by (a reading isomorphic to) its polygonal `D̄`.  FR-FC-1 records reading-INDEPENDENCE; the
reading-EXISTENCE burden shifted to the consumer should be recorded explicitly (it is the same FR-1 shape as
row 91's endpoint hypothesis, so not a defect of 94/162, but the floor lane must plan for it).

RF-3 (`CV.AxEtnyreData`, non-blocking).  `D : SM.SmoothKnotDiagram` — a SMOOTH regular diagram.  CV's "front
diagram" is otherwise polygonal in this development (`Diagram` in `CV.AxHomflyData`).  The consumer's `T` in
d3_floor:926-975 is the smooth rounded front of the lift, so the shape fits, but FR-FC-4 should say
explicitly that row 161 is stated for smooth fronts and a polygonal CV front must first be realised as the
front of a `TransverseKnot`.  Also: the hypothesis "no downward vertical tangency" is discharged as
`(D.vel t).1 = 0 → 0 < (D.vel t).2`; on the class `K.front = D` it is automatic (`front_vertical_up`), so
the Lean theorem's content is independent of it — fine and recorded (FR-FC-4), but note the CV axiom's
point is the LIFT direction (a diagram with no downward vertical tangency IS the front of a transverse knot);
that existence is not in the row and is the consumer's construction (d3_floor:926-973 does it by hand).

RF-4 (`AxSlboundData` normalisation, checked, no flag).  `homfly` in `CV.AxHomflyData` (CV/Axioms.lean:186)
is `SM.homfly = Classical.choose lit_homfly` (LinkInterfaces.lean:131), the same map as in
`AxSlboundData`; `P_eq_homfly` bridges row 94's `P`.  "In the normalization of ax:homfly" is therefore
literal.

RF-5 (`sl` is a definition depending on a proof term, informational).  `slCircle` chooses row 88's radius
through `fd_linking_calculus.transverse_uniform`; the definition of the document's number thus depends on
the accepted row-88 THEOREM (axiom-free), not on any axiom — good; but a reviewer should know that changing
row 88's statement would change the definiens of `sl` (U1a then shows the value is radius-independent).

RF-6 (`IsPositivePushoff`'s parametrisation, no flag).  `T' = fun θ => B(θ, s₀)` is oriented by the
annulus's `θ`, i.e. parallel to `L`; Etnyre's `T₊(L)` carries the same orientation.  The clause quantifies
over all `b` and all `s₀ < b`; large circles are isotopic to small ones through the annulus itself (§1.2.4).

RF-7 (`TransverseKnot.immersion` redundant, no flag).  `vel_ne_zero_of_positive` shows the field adds no
strength; the transverse clause is stated on the printed class regardless.

No red flag found that would make a statement STRONGER than printed; all deviations are weakenings or
narrowings already recorded (FR-SC-2, FR-FC-5) or the FR-1 reading pattern.

## 4. Triviality

* `FdContactData.over_rule_sign` is `rfl`-level on row 92 (it is the printed convention sentence; carries no
  content).  Acceptable — precedent: definitional fields in other bundles — but it should not be counted as
  "proved content" of row 94.
* `FdContactData.front_writhe` is the axiom's field `transverse_front_writhe` VERBATIM; row 94's display
  fd:front-writhe and row 161 (`CV.ax_etnyre`, one line, hypothesis unused) are therefore immediate from the
  axiom.  The printed proof's content for this display (the `det(∂_x, ∂_z, ν) = 1` dictionary identifying
  Etnyre's crossing sign with the campaign sign, sm-3:3432-3441) is NOT formalised: the axiom asserts the
  literature identity directly on the accepted `SmoothKnotDiagram.writhe`.  This is FR-SC-7's content; the
  interface review should treat the sign audit (§1.2.3 above and PLAN §4) as the evidence, since nothing in
  Lean checks it.  Not a defect of the design (the alternative — an axiom in Etnyre's own sign vocabulary plus
  a formal dictionary — has no accepted vocabulary to land on), but it means rows 94(ii)/161 add no
  verification of the sign.
* `CV.ax_slbound := ax_slbound_of fd_contact` is row 94 rewritten with `P_eq_homfly` — by design.
* `src_contact_iff_consequence` PREVENTS a triviality: it shows the ∃-form cannot be satisfied vacuously by
  a strange `r`, `tb` (the clauses pin `r`, `tb` on the class and force the two consequences).  Good.
* `slCircle`'s `else 0` cannot trivialise (P): the pushoff circles ARE in the domain (§1.1), so `0` is never
  the value the clause constrains; if the domain check ever failed for a class member the clause would become
  a FALSE constraint (`w − D = 0`), not a vacuous one — a useful property (a wrong bridge would be caught as
  inconsistency, not hidden).
* Nothing makes `representative_bound` trivially true: `sl K = writhe ∈ ℤ` is real-valued but the bound is a
  genuine inequality against `degAZ (P X)`; it is vacuous only where no reading `X` exists (RF-2).

## 5. Summary for the orchestrator

* Satisfiable: YES (`SrcContactClauses` ⇔ `SrcContactConsequence`, both true on the accepted definitions).
* Axiom truth: TRUE with the accepted conventions (over = smaller `y` / smaller slope, `det_xz`, `+∂_y`
  pushoff, standard Gauss normalisation, `IsDownCusp` = Etnyre's down cusp, `IsPositivePushoff` = Etnyre's
  `T₊`); the direction `w − D` (not `w − U`) is fixed by the `D = 1, U = 3` probe.
* Blocking issues: none.
* Non-blocking: RF-1..RF-3, RF-5 above; PLAN §6 U1a `min → max`; the triviality notes of §4.
* Doubtful leaves: none; effort risks R1 (`u_reading`), R2 (`u_legendrianFront`), R3 (`u_family`) as in PLAN §7.

Probe scripts: `work/drafts/contact/prereview_probe/probe_audit{,2,3,4}.py` with outputs `*.out`
(run with `/workspace/envs/persona/bin/python`, numpy 2.5.1; `probe_audit2-4` import `probe_audit`).
