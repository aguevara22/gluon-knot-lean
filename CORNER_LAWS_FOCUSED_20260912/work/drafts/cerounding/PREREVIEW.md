# PRE-REVIEW — ce:rounding (row 89), fixed statement Statements_FINAL.lean

Independent auditor (pod subagent), 2026-09-14T09:27Z / 5:27AM ET.  This is the PRE-review requested before the formal
fidelity review, not the fidelity review itself.  Inputs: work/drafts/cerounding/Statements_FINAL.lean
(the frozen row statement), Skeleton_FINAL.lean (the chain), PLAN_FINAL.md §6 (risks CE-R1..CE-R11),
work/AUTHOR_NOTES.md entry "Ce:rounding lane (row 89)" (~09:05Z), the accepted vocabulary
work/lean/SM/CeSmoothingRecord.lean (row 90), the printed lemma reference/SM/sm-3-statesum.tex:3029-3062
and its proof 3063-3169 (skimmed for the objects only), row 90's report K-3/K-4.

Commands run (all from work/lean, nothing written there, no `lake build`):
- `lake env lean ../drafts/cerounding/Statements_FINAL.lean`: 0 errors, exactly 1 `sorry` warning (= `SM.ce_rounding`). Confirmed.
- `lake env lean <copy of Skeleton_FINAL.lean + #print axioms>`: 0 errors, 33 `sorry` warnings; `SM.ce_rounding` =
  [propext, sorryAx, Classical.choice, Quot.sound]; `SM.SpatialLink.constWitness`, `SM.SpatialLink.constSmoothing`,
  `SM.CuspRoundingWitness`, `SM.CeRoundingData` = [propext, Classical.choice, Quot.sound]. Panel claims confirmed.
- `lake env lean ../drafts/cerounding/NonVacuity.lean`: 0 errors, 0 warnings, 0 `sorry`; axioms of every declaration
  = [propext, Classical.choice, Quot.sound] (checked on a copy with `#print axioms`).
- two auxiliary kernel checks in /tmp (not deliverables; reproduced in §3/§4 below): `heights_distinct_of_embedded`,
  `CuspRoundingFamily.eq_of_no_cusps`.

## 1. Non-vacuity (CE-R11) — work/drafts/cerounding/NonVacuity.lean (324 lines)

Imports ONLY `SM.CeSmoothingRecord` (no draft of the lane, no extra Mathlib module). Namespace
`SM.CeRoundingNonVacuity`. Kernel-checked, zero `sorry`:

| declaration | statement |
|---|---|
| `circle : SpatialLink 1` | the round unit circle at height 0, `t ↦ (Re E t, 0, Im E t)`, `E t = exp(2πi t)` (= `(cos 2πt, 0, sin 2πt)`): `C^∞`, 1-periodic, injective on the circle (`embedded`), `deriv ≠ 0` (`regular`) |
| `not_isCusp`, `cuspSet_eq_empty`, `noCusp` | no cusp: the projected velocity `(Re, Im)(2πi·E t)` never vanishes |
| `sameT_of_proj_eq`, `not_isDoubleOf`, `occSetOf_eq_empty` | no double point: `E s = E t ↔ SameT s t` (`E_eq_iff`, via `Complex.exp_eq_exp_iff_exists_int`) |
| **`circle_cuspedProjection : circle.CuspedProjection`**, `exists_cuspedProjection` | **the printed input class of ce:rounding is inhabited** (CE-R11 closed for the cusp-free case) |
| `circle_regularGenericProjection : circle.RegularGenericProjection` | the projection is already an ordinary finite regular generic diagram |
| **`constSmoothing : circle.CleanCuspSmoothing circle.projLoop`**, `cleanCuspSmoothing_nonempty` | the row-90 class `CleanCuspSmoothing` WITH `collar` is inhabited (constant/identity smoothing; every per-cusp field vacuous since `cuspSet = ∅`; `agree` is `rfl`) |
| **`constFamily : CuspRoundingFamily circle`**, `cuspRoundingFamily_nonempty`, `constFamily_G` | the constant family `G λ = circle` is a `CuspRoundingFamily` (row 90's object; its K-3 non-vacuity) — the "With no cusps take the constant family" clause, kernel-checked on a concrete link |
| `constFamily_intervals_disjoint_circle`, `constFamily_clean_in` | the three EXTRA clauses of the draft's `CuspRoundingWitness` (`intervals_disjoint_circle`, `U`, `clean_in`) hold for `constFamily`, stated without importing the draft (so the draft's witness structure is inhabited for this link too, by transport) |
| `hasDerivAt_cexp`, `deriv_cexp`, `differentiable_cexp`, `contDiff_cexp_nat`, `contDiff_cexp` | `Complex.exp` is `C^∞` with derivative itself — RE-DERIVED (Mathlib's own proofs from `Complex.exp_bound_sq`) because the import closure of SM/CeSmoothingRecord.lean contains Mathlib's trigonometric BASICS but neither `…SpecialFunctions.ExpDeriv` nor `…Trigonometric.Deriv` (checked by `#check`: `Real.hasDerivAt_cos`, `Complex.hasDerivAt_exp`, `Real.contDiff_cos` are all unknown under that import). ~20 lines; keeps the "imports SM.CeSmoothingRecord only" constraint literally |

What is NOT proved (deliberately, budget): a CUSPED witness of `CuspedProjection` (a link with a genuine exact
cusp germ), hence no kernel check that the PER-CUSP fields of `CleanCuspSmoothing` (`disc`, `center`, `clean`,
`arc_in`, `arc_simple`, `collar`, `inside`, `regular`, `simple`, `no_crossing`) are jointly satisfiable — for the
cusp-free link they are all vacuous. Two remarks on this:
- Row 90's report K-4 records that the ancestor class `GeomRounding` v1 "was found empty and repaired"; the
  repaired shape (closed arc in `clean`, `arc_in`, `arc_simple`) is what `CleanCuspSmoothing` inherits. A cusped
  witness is therefore not a formality. But it is EXACTLY what Skeleton_FINAL's `Choices.smoothing` constructs for
  every cusped input once the 33 leaves close — the row's own proof is the kernel check of per-cusp consistency,
  PROVIDED a cusped `CuspedProjection` exists at all (otherwise `exists_family` is vacuous on cusped inputs).
- A cusped `CuspedProjection` witness in Lean needs a globally defined smooth closed curve that equals the exact
  polynomial germ on an open parameter interval and closes up elsewhere: a smooth cutoff (`Real.smoothTransition`,
  NOT in the closure — an extra Mathlib import) plus a global injectivity argument; estimate 300-500 lines. The
  mathematics is unproblematic (§2). RECOMMENDATION: a small follow-up unit, non-blocking for the row's statement.

## 2. Satisfiability of the bundle (`CuspRoundingWitness`, `CeRoundingData`) — VERDICT: SATISFIABLE

Method: (a) the cusp-free circle — kernel-checked above for every field of `CuspRoundingFamily` and the three
extension clauses; `const_of_no_cusps` is exactly `constWitness` (Skeleton, axiom-clean). (b) a concrete cusped
example, checked by hand field by field, plus a hunt for contradictory field combinations.

**The cusped example.** One circle; `y₀ = 0`, `A = 1`, cusp parameter `t₀ = 1/2`. On `(t₀−δ, t₀+δ)` put `u = t − t₀`
and `T t = (u², u, (2/3)u³)` (the exact germ with `x₀ = z₀ = 0`, `y' = 1 ≠ 0`). Projection `(u², (2/3)u³)`: the
standard semicubical cusp at the origin, regular for `u ≠ 0` (`x' = 2u`), injective on the interval (`z` strictly
monotone). Close up: continue the plane curve from the two germ ends `(δ², ±(2/3)δ³)` by a simple regular arc
through `x > δ²` (a "teardrop" with the cusp pointing left), agreeing with the polynomial germ on end collars and
deviating through a flat cutoff so the loop is `C^∞`; take `y` any smooth 1-periodic function equal to `u` on the
germ interval. Then:
- `SpatialLink`: `smooth`, `periodic` by construction; `embedded` because the projection is a simple closed curve
  (injective on the circle), so no two distinct circle points share even the xz image; `regular`: off the germ
  interval the projection is regular; on it `y' = 1`.
- `CuspedProjection`: `cusps_finite` (one cusp, `{(0, 1/2)}`), `exact_germ` (by construction, `δ` as chosen),
  `doubles_finite` (`occSetOf = ∅`), `transverse`/`no_triple`/`heights_distinct` vacuous. (Add a twist away from the
  cusp for a version with one transverse crossing at distinct heights: nothing changes below.)
- Conclusion (the printed construction with the time clamp `μ = smoothTransition λ`): `Δx = μ ε u ρ(u)`, `Δy = 0`,
  `Δz = 0` (`y₀ = 0`), `ρ` a cutoff supported strictly inside the cusp interval `(a, b) = (t₀−b', t₀+b')`.
  `start` (`μ(0) = 0`); `fixed_outside` (support of `ρ`); `a_lt`, `lt_b`, `len` (`b' < 1/2`);
  `intervals_disjoint`/`intervals_disjoint_circle` vacuous (one cusp); `generic` for `λ ∈ (0,1]`: `μ > 0`, projected
  velocity at `u = 0` is `(με, 0) ≠ 0`, elsewhere `z' = 2u² ≠ 0`; no doubles (clearance keeps the moved arc inside
  `U`, which the rest of the curve avoids); `clean`/`clean_in` with ONE `U` for all `λ` (the chart rectangle of
  Skeleton §4.2/4.3, or a disc adapted to `(a,b)`, see (iii)); `same_doubles`: both sides empty (`False ↔ False`);
  `same_data` vacuous; `smooth_embeddings_start`: joint `C^∞` on `ℝ × ℝ` (`μ` smooth, cutoff smooth), embedded and
  regular slices for ALL real `λ` because `μ ∈ [0,1]` and `Δy = 0` (spatial injectivity from projected injectivity
  + heights; spatial regularity from `y' = 1` on the arc and `L`'s own regularity elsewhere); `circles_retained`:
  periodicity of the periodised cutoff; `const_of_no_cusps`: not applicable (`cuspSet ≠ ∅`).

**Contradiction hunt (field combinations examined; none contradictory).**
- (i) Time clamp vs `start`/`generic`: `smoothTransition 0 = 0`, `= 1` on `[1,∞)`, `∈ (0,1)` on `(0,1)`
  (`pos_of_pos`, `lt_one_of_lt_one`, `projIcc`), `C^∞`. So `G 0 = L` exactly, every `λ > 0` gives a positive slice,
  `G λ = G 1` for `λ ≥ 1` and `= L` for `λ ≤ 0`. No field mentions `λ ∉ [0,1]` except the type-level
  embedded/regular/joint-smooth demands, met by constancy there. Consistent.
- (ii) `intervals_disjoint_circle` (all `n : ℤ`) with `len` and `a_lt`/`lt_b`: two cusps on one circle have distinct
  parameters in `[0,1)` (as elements of `cuspSet`), so intervals shorter than half the circular gap are disjoint
  modulo 1. Consistent; strictly stronger than the library's `intervals_disjoint` (`n = 0`), which admits wrap-around
  overlap (e.g. `(0.9, 1.3)` vs `(0.1, 0.4)`): a genuine improvement, not a contradiction.
- (iii) `clean_in` ties `cs.a = a`, `cs.b = b`, `cs.U = U` for EVERY `λ ∈ (0,1]`, and `CleanCuspSmoothing.clean` says the
  projection meets the CLOSED disc `U k` only along the CLOSED arc `[a k, b k]` while `arc_in` puts that arc inside
  `U k`. Hence the projected arc must EXIT `U k` exactly at the parameters `a k`, `b k` and never re-enter: `U` and
  `(a, b)` are coupled, and a naive "small disc + slightly longer interval" violates `clean`. Satisfiable: the
  skeleton's rectangle `[−M², 2M²] × [u₋³, u₊³]` in chart coordinates has `Z = u³` running exactly over the arc's
  range, so the arc leaves through the top/bottom edges at `a`, `b` and, `Z = u³` being monotone, the rest of the
  chart arc lies outside (the printed ce:cubic-difference). Consistent, but this coupling is the one place a
  reviewer should look when the U-C leaves `clean`/`arc_in` are closed. (Inherited from the accepted `GeomRounding`
  v2 shape, K-4.)
- (iv) `no_triple : IsDoubleOf p q → IsDoubleOf q r → IsDoubleOf p r → False` with integer translates: for a genuine
  crossing `(p, q)` and `r = p + 1`, `IsDoubleOf q r` holds but `IsDoubleOf p r` FAILS (`SameParam p r`), so the field
  is not violated by translates; it is exactly "no three pairwise-distinct circle points share an image".
  Satisfiable with crossings.
- (v) `ExactCuspGerm` with a large `δ`: a strictly monotone `y` on an interval of length `≥ 1` contradicts
  periodicity, so any witness of the `∃ δ` has `δ ≤ 1/2` implicitly; the skeleton shrinks to `min δ (1/3)`. No
  contradiction (`∃`, not `∀`).
- (vi) `CleanCuspSmoothing.disjoint` (discs of DIFFERENT cusps disjoint, across circles too) with `center`: needs
  distinct cusp images; two cusps with one image would be a double point at a cusp, excluded by `transverse`
  (`CuspedProjection.not_isCusp_of_isDouble`, proved in Statements_FINAL). Consistent.
- (vii) `same_doubles` quantifies over ALL `p q : Fin c × ℝ` (not only the fundamental period): fine, both sides are
  periodic in each argument.
- (viii) `no_crossing` at the arc ENDPOINTS (`q = (k, a k)`, not in the open arc, so `G q = xz(L) q ∈ U k` by
  `arc_in`): the new arc must avoid the two endpoint images — true for `Z = u³` strictly between the end values
  (skeleton `arc_no_crossing` case 3, listed as a false-leaf probe in CE-R10). Consistent.
- (ix) `heights_distinct` in `RegularGenericProjection` for the slices vs `Δy = 0`: heights literally unchanged.
- (x) `const_of_no_cusps` demands a witness with `∀ λ, G λ = L`, while `exists_family` for the same `L` may return
  another witness: no conflict, and in fact EVERY witness of a cusp-free `L` is constant (kernel-checked in /tmp:
  `CuspRoundingFamily.eq_of_no_cusps`, from `fixed_outside` applied vacuously at every parameter). So the two
  readings of the printed sentence (B: "some witness is constant", A: "every witness is constant") coincide.

## 3. Fidelity red flags (statement vs sm-3:3040-3062)

Clause coverage (hypotheses 3031-3046, conclusion 3047-3057) — every printed clause has a Lean counterpart
(Statements_FINAL header tables verified line by line); the two closing disclaimers (3055-3057) assert nothing and
correctly have no field. "isolated" is implied by finiteness; "cusps on another branch" is a proved consequence
(`not_isCusp_of_isDouble`). No printed clause is missing.

Fields with no printed counterpart, and whether each is a recorded risk:
| field / feature | recorded? | assessment |
|---|---|---|
| `SpatialFamily` indexed by all of `ℝ`, slices embedded everywhere, joint `C^∞` on `ℝ × ℝ` | CE-R2 | see below — NOT blocking |
| `CuspRoundingWitness.U`, `clean_in`, `intervals_disjoint_circle` | CE-R6 | see below — NOT blocking |
| `heights_distinct` kept though derivable from `embedded` | CE-R3 | confirmed derivable (kernel-checked in /tmp, `heights_distinct_of_embedded`, 12 lines); keeping the printed field is the right call |
| `IsDisc` = CONVEX compact with nonempty interior for "clean cusp neighbourhood" | row 90's K-5, NOT in CE-R1..R11 | inherited from the accepted vocabulary; an unprinted restriction on the CONCLUSION (the row asserts a convex neighbourhood exists — stronger, and supplied by the construction). Suggest citing K-5 in the row-89 notes; not blocking |
| `0 < c` absent from bundle fields 2-6 (they quantify over any `c`, incl. `c = 0`) | CE-R8/K-6 partly | harmless: those fields are projections of a witness |
| `RegularGenericProjection.no_triple`/`heights_distinct` beyond SM's diagram definition (sm-3:339-343: "regular smooth immersion with finitely many transverse double points") | CE-6 | implied by "only coincidences are double points" and required for the height over-rule; faithful |
| bundle fields 2-6 are ∀-over-witness projections | CE-R7 | equivalent to "∃ W with these properties" since they are fields; adds no content, removes none |

**CE-R2 (family on ℝ via the `smoothTransition` clamp) — both sides.**
- For blocking: the printed object is a family on `[0,1]`; the Lean `fam.G` on `[0,1]` is the printed family in the
  REPARAMETRISED time `μ = φ(λ)` (`φ' = 0` at `0` and `1`), not the printed formula `X_λ = u² + λεuρ`; the type also
  asserts embeddedness for `λ ∉ [0,1]`, which the paper explicitly does not claim (sm-3:3103-3104).
- Against blocking (my assessment): the row is an EXISTENCE statement and the two readings are inter-derivable.
  Lean ⇒ printed: restrict a global jointly-smooth family to `[0,1]`. Printed ⇒ Lean: compose any printed family with
  `φ` (jointly smooth; slices for `λ ≤ 0` and `λ ≥ 1` are `L_0` and `L_1`, both embedded) — so no strength is added
  or lost, and the reparametrisation is invisible in the statement (it lives inside `exists_family`). The
  alternative literal strip reading (`ContDiffOn … (Icc 0 1 ×ˢ univ)`) would require editing the ACCEPTED
  `SpatialFamily` (row 90) and buys nothing. Verdict: non-blocking; must be cited in the review with the
  inter-derivability argument above.
**CE-R6 (witness extension) — both sides.**
- For blocking: the row's conclusion is STRONGER than the accepted `CuspRoundingFamily` and than the memo; `cs.a = a`,
  `cs.b = b` (smoothing arcs = fixing intervals) and one `U` for all `λ` are not sentences of the statement; row 90
  quantifies over the parent, so the extension is asserted by row 89 alone.
- Against blocking (my assessment): a stronger PROVEN conclusion is not a fidelity defect; the added clauses are the
  literal reading of "fixed outside disjoint cusp parameter intervals … It cleanly smooths the cusps" (one set of
  intervals for both sentences, "disjoint" on a circle) and of the printed proof ("Each modified portion is one
  regular embedded oriented arc in a clean cusp neighbourhood" with one `V` per cusp chosen once); the parent is
  delivered by `toCuspRoundingFamily`. Note that `intervals_disjoint_circle` REPAIRS a weakness of the accepted
  parent (wrap-around overlap, §2(ii)). Verdict: non-blocking; D-2 (no fold-in, since row 90 is accepted) is the
  correct handling; cite in the review.

## 4. Triviality — nothing found

- `exists_family` is not trivial for cusped inputs: the constant family fails `generic` (a cusp is a zero of the
  projected velocity), and any witness must change `T` on intervals of length `< 1` around each cusp only.
- For cusp-free inputs the row IS trivial (constant family) and forced (`eq_of_no_cusps`), which is what the printed
  sentence says.
- Bundle fields 2-6 are tautologies of the witness structure (CE-R7): harmless, no printed content lost.
  `const_of_no_cusps` is derivable from `exists_family` + `eq_of_no_cusps` but stands for a printed sentence.
- The hypothesis class is inhabited (§1), so `exists_family` is not vacuous; whether it is vacuous on CUSPED inputs
  is not kernel-checked (§1, follow-up), though mathematically clear (§2).
- No definition (`IsCusp`, `cuspSet`, `IsDoubleOf`, `RegularGenericProjection`, `CleanCuspSmoothing`) collapses to
  `True`/`False`; `crossSignOf`/height clauses carry real content.

## 5. Summary for the orchestrator

Blocking: none.
Non-blocking (to record/cite): (1) no kernel-checked CUSPED `CuspedProjection` witness — recommend a follow-up unit
(~300-500 lines, needs `Real.smoothTransition` import) or accept the Skeleton's `Choices.smoothing` (once the 33 leaves
close) as the per-cusp consistency check; (2) CE-R2 and CE-R6 should be cited with the inter-derivability / stronger-
conclusion arguments above; (3) add row 90's K-5 (`IsDisc` convexity) to the row-89 risk list; (4) the
`clean`/`arc_in`/`clean_in` coupling of `U` to `(a,b)` (§2(iii)) is the one satisfiability subtlety — watch the U-C
leaves `clean`, `arc_in`, `arc_simple`; (5) `heights_distinct` is redundant given `embedded` (12-line proof) —
keep it, say so; (6) NonVacuity.lean re-derives `Complex.exp` differentiability to honour the import constraint —
if the reviewer prefers, replacing §0 by `import Mathlib.Analysis.SpecialFunctions.ExpDeriv` is a 2-line change.
