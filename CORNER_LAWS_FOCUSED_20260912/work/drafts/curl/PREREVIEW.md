# PREREVIEW — cf:lem-curl fixed statement (work/drafts/curl/Statements_FINAL.lean)

Independent auditor, 2026-09-14 06:41 UTC / 2:41am ET. Scope: pre-review (not the formal fidelity
review) of the fixed statement for row 98 cf:lem-curl, printed at reference/SM/sm-3-statesum.tex:3870-3891,
proof 3892-4280 skimmed for the objects; consumer cf:thm-carrierfloor (C) at 4423-4455. Recorded risks read
from PLAN_FINAL.md §7 and work/AUTHOR_NOTES.md:4049-4067 ("Curl lane"). Check environment: `source
/workspace/envs/lean/env.sh; cd work/lean && lake env lean ../drafts/curl/Statements_FINAL.lean` — 0 errors,
1 `sorry` (line 381, the row `SM.cf_lem_curl`), 6.6 s. Nothing written under work/lean. Numeric probe script:
work/drafts/curl/prereview_probe.py (python3, seed 20260914; 0 failures).

**Verdict: satisfiable and non-trivial; no blocking issue found. FR-C1 is the one point a strict reviewer
will debate; it is recorded and defensible, and two cheap mitigations are suggested below.**

## 1. Non-vacuity: are CurlSite, RecordCarried, CurlWitness, CurlData jointly satisfiable?

Method: (a) field-by-field consistency check of the conventions (windows mod 1, [0,1) parameters, the ∃! and
the signs); (b) a concrete site — the unit circle — built numerically through the printed construction
(model c, b; cuts; affine fit A; Φ ∘ c), with every witness clause checked; (c) an asymmetric second site
(a perturbed ellipse, six base points, three cut levels, cuts by IVT) to make sure nothing depends on the
circle's symmetry.

### 1a. The concrete site (circle)
`F.γ t = (cos 2πt, sin 2πt)` (SmoothRegularLoop: C^∞, 1-periodic, `deriv ≠ 0`). `D` = any one-component
crossing-free polygonal `Diagram` (the corpus constructs such diagrams: `Shadow.single … .positiveDiagram`,
`GeoPositiveLift.lean:738`, `LinkPositiveLift.lean:834` prove `IsCrossingFreeCircle`). `RecordCarried F D`:
`one` ✓; `Visit` is empty so `τ`, `τ_mem`, `τ_inj`, `twin_eval`, `transverse`, `order`, `sign_eq` are vacuous;
`doubles` holds because the circle is injective on [0,1). `u = (0,1)`, `t₀ = 0`, `tangent_at` ✓;
`α, β = ∓1/8` (`short` ✓), `embedded` ✓, `no_double` vacuous, `θ t = 2πt + π/2` is an `IsLiftOn` and
`StrictMonoOn` ✓, `isolated` ✓ (tangent = u only at integers). So `CurlSite` is inhabited; the consumer's
sites are inhabited too (every field is supplied by a `RoundingWitness` junction: `θ_lift`, `θ_strict`,
`direction_once`, `same_strands`, `junction_embedded`, the subdivision gives `b j − a j < 1`).

### 1b. The witness on that site (numerically, for δ = 0.05, 0.02, 0.01, 0.003)
Cuts `s₁, s₂ = ∓δ` (`ξ(s₁) = ξ(s₂)` by symmetry), `ℓ = η(s₂) − η(s₁) > 0`; `a = c = sin 2πδ > 0`,
`b = d = cos 2πδ > 0`; `T₋ = a v + b u`, `T₊ = −c v + d u` verified; `x, y` from the printed formulas.
Checked on the glued curve (old circle on [s₂, s₁+1] + Φ ∘ c on [−2, 2]):
- endpoints and endpoint tangent rays match with positive scale (C¹ join) ✓;
- rot(F') = 0 = rot(F) − 1 (numerical total turning, error < 2·10⁻³) ✓ — **(iv) rot**;
- the inserted arc has no tangent `u` and exactly one tangent `−u`; the tails of F inside the disc have
  tangent angle in (−π/2, π/2), so neither ✓ — **(ii)**;
- exactly one double point Φ(±1), `det(Φ'(1), Φ'(−1)) < 0` (later branch over ⇒ negative), inside the
  disc ✓ — **(iii)**; writhe of D' = 0 − 1 ✓ — **(iv) w**;
- transverse excess: every interior inserted point has `ξ > ξ(s₁)`, every tail point `ξ < ξ(s₁)` ✓, so
  the inserted arc meets the tails only at the joins (no extra double point; `doubles_outside`,
  `one_double` consistent);
- the disc (radius = max distance of the two window arcs from p) is small enough that its intersection
  with the circle lies in the arc [α, β] ✓ — `disc_meets_arc`; `x → 0`, `ℓ → 0` with δ ✓.
The asymmetric site behaved identically (18 (t₀, level) cases; rot drops by exactly 1 each time).

### 1c. Field-combination checks (no contradiction found)
- **Window mod 1.** `unchanged`/`unchanged_deriv` hypothesis `∀ n : ℤ, t + n ∉ Ioo s₁ s₂` with
  `s₂ − s₁ ≤ β − α < 1`: the endpoints `s₁, s₂` themselves are "off the window", so the fields demand
  `F' = F` *with velocity* at the cuts — true for the C^∞ glued curve, and exactly what `SmoothCurl`/
  `exists_loop_of_arc` deliver. When the window straddles an integer (my circle site: `s₁ < 0 < s₂`)
  `fract q₁ > fract q₂` is possible; `RecordCarried` only needs the pair `(τ' under, τ' over) = (fract q₁,
  fract q₂)` to be a `doubles` witness and to be cyclically adjacent — `cycBetween_fract_pair` covers the
  wrap (e.g. `cycBetween τ 0.9 0.1` holds for `τ ∈ (0.1, 0.9)`). Consistent.
- **Lift on the arc, `β − α < 1`.** `IsLiftOn` + `StrictMonoOn θ (Icc α β)` + `isolated`: compatible (the
  sweep is then < 4π, and `isolated` is genuinely extra content, FR-C5). The disc is chosen to meet F only
  on a sub-arc with `|θrel| < π/2` (`exists_chart`, `exists_disc_in_chart`), so `one_neg_u` is not
  threatened by a `−u` tangency elsewhere on a long arc; `SmoothCurl.tails_no_neg_u` carries this.
- **`∃! t ∈ Ico 0 1` for `−u`.** Unique parameter ⇔ unique point here: two parameters at one point would
  be the double point, whose two tangents have `det ≠ 0`, so they cannot both be `−u`.
- **Unique double point in Δ, sign −1, together with `RI D D'`, `P D' = P D`, `writhe_eq`.** The polygonal
  kink is a clockwise monogon with the later branch over: `D'.sign kink = sgn det(dir over, dir under) =
  sgn det(later, earlier)`; the smooth model gives `det(c'(1), c'(−1)) = −8 < 0` and `det A > 0` preserves
  it; `RecordCarried.sign_eq` for the kink then reads `sgn det(F'(q₂)', F'(q₁)') = −1 = D'.sign kink` —
  the same convention as `SmoothCurl.double_neg` and `KinkInsertion.order_pair` (under = earlier). Writhe
  of D' = old signs + (−1) ✓. `RIData U D D'` has D crossing-free in U and D' with the kink; `RI D D'` is
  the `Or.inl` branch; `P_reidemeister_I : RI D D' → P D = P D'` (PolynomialBlock.lean:605) gives
  `poly_eq` by `.symm` ✓.
- **rot − 1 and writhe − 1 together.** A clockwise kink with later-over is exactly the configuration where
  both drop by one (verified on the circle: rot 1 → 0, w 0 → −1). No tension between (iii) and (iv).
- **`doubles_outside`.** F has no double point in Δ (Δ ∩ F ⊆ arc, arc carries no occurrence), F' has
  exactly the new one there; outside Δ the curves agree as sets. Consistent with `RecordCarried F' D'`
  (`doubles`: old pairs, the kink pair; cross pairs excluded by the transverse excess).
- **`old_point`, `old_sign`, `old : D.Crossing ≃ {y // y ≠ kink}`.** Satisfied by `τ' = τ` on old
  occurrences (`CarriedAssembly.τ_old`) and `F' = F` there; `KinkInsertion.oldVisit_over` supplies the
  visit correspondence.
- **`IsDisc Δ`, `p ∈ interior Δ`.** The closed Euclidean disc `disc S r` is convex, compact, with p in its
  interior (also in the product metric on `ℝ × ℝ`) ✓.
- **`KinkLocation`.** For the crossing-free `D` of my site its `gap` clause is vacuous and any interior
  edge point off the other edges works; with crossings, the open gap of the polygon corresponding to
  `t₀`'s gap among the `τ` (by `carried.order`) has positive length and contains such points. The RI disc
  `U` (in `RIData`) carries no relation to `Δ` — by design (FR-C1/FR-C9), see §2.

## 2. Fidelity red flags

### 2a. Printed clauses → fields (every clause has a field)
3871-72 rot conventions → `toClosedC1Curve.rot` (only the smooth rot occurs). 3873-74 "connected C^∞
immersed circle, one component, finitely many transverse double points, no triple points" → `F :
SmoothRegularLoop`, `RecordCarried` (`one`, finite `Visit`, `transverse`, theorem `no_triple`). 3874 "given
with an oriented diagram" → `D`, `carried`. 3874-75 p, u → `t₀`, `u`, `tangent_at`. 3875 "isolated" →
`isolated` (on the arc; equivalent after shrinking the arc, FR-C5). 3876 "embedded arc … no double point"
→ `α β`, `embedded`, `no_double`. 3877 "turns strictly positively" → `lift`, `turns_pos`. 3878-79
"modified inside a disc Δ meeting the rest of the diagram only in that arc" → `CurlWitness` window fields,
`unchanged` (+`unchanged_deriv`), `new_in_disc`, `old_in_disc`, `disc`, `p_mem`, `disc_meets_arc`;
existence `exists_curl` (Δ ⊆ Δ₀) / `exists_curl'` (as printed). (i) → `F'`, `D'`, `carried'`, `ri`,
`poly_eq`, `doubles_outside`, `old`, `old_point`, `old_sign`. (ii) → `no_u`, `one_neg_u`. (iii) →
`kink`, `kink_mem`, `one_double`, `kink_neg` (`kink_smoothSign`); the kink point is a double point of F'
by `RecordCarried.doublePoints_eq`, so "exactly one" is fully captured. (iv) → `rot_eq`, `writhe_eq`
(`smoothWrithe_eq`). No printed clause is without a field.

### 2b. Fields without a printed counterpart
All are in FR-C6 (window `s₁ s₂` and its bounds, `unchanged_deriv`, `old_in_disc`, `disc_meets_arc`, `ri`,
`old`, `old_point`, the smooth-sign/writhe corollaries), FR-C2 (`exists_curl` with Δ₀), FR-C3 (parametrised
equality with velocity), FR-C5 (`short`, `isolated` on the arc, `θ` as data), or FR-C1 (`RecordCarried`).
The `CurlData` clause fields are tautological projections of `CurlWitness` (the accepted FR-R5 pattern).
I found no unrecorded field.

### 2c. FR-C1 — will a strict reviewer call record-level carrying a blocking class change?
*Case for blocking.* (1) The accepted Rounding.lean §4 docstring declares `Carried` "the one smooth-diagram
notion for cf:lem-rounding, cf:lem-curl and cf:thm-carrierfloor"; the curl lane now introduces a second,
strictly weaker notion for the output, so the printed "(i) is again *such* an oriented diagram" is not
formalised in the class F was given in (input `Carried` via `toRecordCarried`, output only `RecordCarried`).
(2) Under `RecordCarried` the polygon D' is geometrically decoupled from F' everywhere, not just at the
kink: nothing ties `D'.Γ.crossingPoint` to any point of the plane near F', and the RI move happens in a
disc `U` unrelated to Δ. A reviewer may say the printed lemma "modifies the diagram inside Δ" while the
formal polygonal diagram is modified somewhere else; and that `P_{F'}` (the polynomial of the *smooth*
diagram) is identified with `P D'` by convention (FR-R1) rather than by a formal record-isomorphism
theorem in the statement. (3) Downstream: any consumer expecting `Carried` after a curl breaks; the
consumer must be told (FR-C1 says so).
*Case against blocking.* (1) The printed corpus defines diagrams by records (def:gauss-record;
lem:gauss-pl-model "the crossing names, the four-ray orders, the traversal direction and the over/under
designations are retained"), and the accepted front block's `SmoothFront.Marking` (FrontSmooth.lean:1001)
is record-level with no point coincidence — precedent in the accepted corpus for exactly this reading.
(2) The printed proof's own last paragraph establishes `P_{F'} = P_F` by a record isomorphism
(rp:record-polynomial), i.e. at record level; the formal reading uses the printed mechanism. (3) Every
printed conclusion is about the smooth curve (double points, tangents, rot) or about the record (signs,
writhe, P); the polygon's geometry enters no printed clause. `RecordCarried` still yields "finitely many
transverse double points, no triple points, over/under at each" (`doubles`, `transverse`, `no_triple`,
`sign_eq`), which is all "such an oriented diagram" asserts. (4) `Carried.toRecordCarried` means no domain
narrowing; the alternative (B) adds unprinted hypotheses, a worse violation under the handoff rules.
(5) It is forced: with the accepted local `RIData` the polygon's gap stretch may be far from p, so no
polygon D' with a kink *at* the smooth double point and agreeing with D outside a disc exists in general.
*My estimate:* a strict reviewer will flag it and ask for the class change to be stated in the row's
docstring and AUTHOR_NOTES (done), and to be told what is lost; it is unlikely to be judged blocking if two
things are added (both cheap, both available from the skeleton): (a) export `old_crossingPoint : ∀ x,
D'.Γ.crossingPoint (old x).1 = S.D.Γ.crossingPoint x` (from `KinkInsertion.old_point`), so that when the
input is `Carried` the output is "Carried at every old crossing, record-level only at the kink" — the
deviation becomes the one unavoidable point; (b) at port time amend the Rounding.lean §4 docstring's
"one notion for … cf:lem-curl" sentence (or record in AUTHOR_NOTES that it is superseded for the curl
output). Also state explicitly in AUTHOR_NOTES that the RI disc `U` of `ri : RI D D'` is unrelated to Δ.

## 3. Triviality
None. `CurlSite` is inhabited (§1a), so `exists_curl` is not vacuous. `CurlWitness S Δ` cannot be inhabited
by `F' = F`, `D' = D` (`rot_eq`, `writhe_eq` forbid it), nor by a degenerate Δ (`IsDisc` requires compact,
`p ∈ interior Δ` requires nonempty interior). `exists_curl'` is derivable from `exists_curl` (Δ₀ = univ) —
redundant, not trivialising. The clause fields of `CurlData` are projections (FR-R5) and add no content;
the content is `exists_curl` + the field list of `CurlWitness`.

## 4. Numeric probe (prereview_probe.py; 0 failures)
Unit MF (11 leaves + docstring identities): `hasDerivAt_cModel/bModel` (finite differences, 2000 random t);
`c(±2) = b(±2) = (3, ∓6)`; `b'(±2) = (3/11) c'(±2)`; `c'(∓2) = 11(±q v₀ + u₀)`, q = 4/11; `c'(0) = −u₀`;
`det(c', c'') = −2(1+3t²)`, `det(b', b'') = 18/11`; `cModel_double` (grid scan: only {−1, 1});
`det(c'(1), c'(−1)) = −8`; `fitA_ray_minus/plus`, `det_fitA = x > 0`, `yFit_bound |qy| < 1`, `xFit_pos`,
`1 − (qy)² = 4abcd/(bc+ad)²`, `fitA_add/smul`, `fitA_u₀ = u`, `fitA_v₀ = xv + yu`, `orderedRay_condition`
(both determinants, arbitrary-sign a b c d) — 3000 random (a,b,c,d) over six decades, random frames.
`inserted_arc_props` (Unit R, built on MF): Φ(−2) = p₋, Φ(2) = p₊, endpoint derivative = positive multiple
of T∓, Φ(−1) = Φ(1), `det(Φ'(1), Φ'(−1)) < 0`, excess = (ℓx/12)(4 − t²) > 0 on (−2, 2), diameter
`|Φ(t) − p₋| ≤ ℓ(x + 2)`, `0 ≤ 6 + t³ − t ≤ 12` — 1500 random cases. Unit G chart formulas on random
smooth curves: `η' = |F'| cos θrel`, `ξ' = −|F'| sin θrel`, `T = −sin θrel · v + cos θrel · u`,
`det(v, u) = 1`, `⟨v, u⟩ = 0`. Unit HT with Mathlib's `Real.smoothTransition` (φ = e(x)/(e(x)+e(1−x)),
e(x) = exp(−1/x)): φ' ≥ 0, φ = 0 on x ≤ 0, φ = 1 on x ≥ 1; `deriv_blend_ge` (h' ≥ f'), `sep_of_deriv`,
`blend_between`, `blend_eq_left/right`; mirrored collar `deriv_blend_le` (h' ≤ f'), separation g ≥ f —
300 random (f, g, e, λ) each, 51 grid points per collar. Unit T: ((Δθ − 2π) − Δθ)/2π = −1.
**No identity failed.** Remark: `hpos`/`hneg` in `deriv_blend_ge/le` are not needed for the stated
inequalities (only `g' ≷ f'` and the separation are) — harmless extra hypotheses.

## 5. Recommendations (non-blocking)
1. Add `old_crossingPoint` to `CurlWitness` (and to `CurlData.i`) — see §2c(a).
2. AUTHOR_NOTES: say that the RI disc `U` is unrelated to Δ, and that Rounding.lean §4's "one notion"
   sentence is superseded for curl outputs; amend that docstring at port time.
3. Optional: an `example`/`def` building a `CurlSite` from a `RoundingWitness` junction (the consumer's
   entry) would document non-vacuity formally; `CurlSite.ofCarried` already has the right signature.
4. Optional: a one-line docstring on `one_neg_u` noting parameter-uniqueness in [0,1) equals
   point-uniqueness (two parameters at one point would be the double point, whose tangents are transverse).
