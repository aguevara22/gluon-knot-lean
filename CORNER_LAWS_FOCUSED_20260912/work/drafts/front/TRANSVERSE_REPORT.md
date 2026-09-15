# TRANSVERSE_REPORT — row 92, Definition def:transverse-front (frame SM15)

Unit: statement unit for def:transverse-front on the smooth class (AUTHOR_NOTES 2026-09-14 ~04:38Z, lane (b)).
File: `work/drafts/front/TransverseFront.lean` (914 lines, 135 declarations; imports `SM.FrontGeomModel`, hence
`SM.FrontRecordBridge`, `SM.FrontSmooth`).  Intended home: `work/lean/SM/TransverseFront.lean`.
Main declaration: `SM.transverse_front_definition : TransverseFrontDefinitionData` (13 fields).
Compile: `cd work/lean && lake env lean ../drafts/front/TransverseFront.lean` — 0 errors, 0 warnings, no placeholders,
no new axioms.  `#print axioms` (on a /tmp copy) of `SM.transverse_front_definition`, `SM.SmoothFront.comp_ne_xz`,
`SM.TransverseKnot.exists_vertical_tangent`, `SM.SmoothKnotDiagram.card_occSet`: `[propext, Classical.choice, Quot.sound]`.
Written 2026-09-14 (pod, tmux `side`).

## 1. The printed text (reference/SM/sm-3-statesum.tex:3328-3340, verbatim)

"In (ℝ³, ker(dz − y dx)), a generic positive transverse front is the oriented knot diagram in the (x,z) plane obtained
from a smooth oriented embedded knot T with z′ − y x′ > 0 whose xz projection is an immersion of the parameter circle
with finitely many transverse double points and no triple point, the over strand at each double point being the branch
of smaller y. It has no cusp. At a vertical tangent, x′ = 0, the inequality gives z′ > 0: every vertical tangent of a
generic positive transverse front points upward, a consequence and not a hypothesis. The diagram determines its writhe
and its over/under counts; the knot T is named separately where it is used."

Read for consumption only (no clause of theirs is stated here): src:contact (3342-3366) — "For a generic positive
transverse front (Definition def:transverse-front), self-linking equals its front writhe"; fd:contact (3404-3430) —
"In the xz front page the smaller-y branch is over, and its crossing sign is sgn det_xz(u_O, u_U). For a generic positive
transverse front (Definition def:transverse-front) one has sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))"; "Let T be an
individual smooth positive transverse knot whose specified xz projection D_T is an ordinary finite regular generic
diagram"; proof 3431-3441 (observer on the negative-y side; det_xyz(∂x, ∂z, ν) = 1; ad − bc = det_xz).  Also
cf:thm-carrierfloor(C) 4510-4523 ("Its front and its smaller-y over/under assignments are exactly the diagram T") as
the other consumer of the vocabulary.  Objects the consumers name: the knot T (`TransverseKnot`), its front (`K.front`),
the double points q (`crossingPairs`), the over/under tangents u_O, u_U (`vel` of the over-first pair), the crossing
sign sgn det_xz(u_O, u_U) (`crossSign`, `crossSign_eq_sign`), the writhe Σ_q (`writhe`); sl(T) is NOT defined in this
document (cv-lane-plan §161) and is not defined here.

## 2. Clause → field map (bundle `TransverseFrontDefinitionData`)

| # | printed clause (tex lines) | field | rendered as |
|---|---|---|---|
| 1 | "In (ℝ³, ker(dz − y dx))" (3329) | `contact_space` | `Space = ℝ × ℝ × ℝ`, `(x,y,z) = (p.1, p.2.1, p.2.2)`; `contactForm p v = v.2.2 − p.2.1 * v.1` (α_p(v) = v_z − p_y v_x) |
| 2 | "a smooth oriented embedded knot T" (3330-3331) | `knot` | `ContDiff ℝ ∞ K.T`, `Function.Periodic K.T 1`, `K.T s = K.T t → SameT s t`, `deriv K.T t ≠ 0` (the last a consequence, `deriv_T_ne_zero`) |
| 3 | "with z′ − y x′ > 0" (3331) | `positive` | `0 < deriv (zOf K.T) t − yOf K.T t * deriv (xOf K.T) t`, and this equals `contactForm (K.T t) (deriv K.T t)` (`deriv_T`: T′ = (x′, y′, z′)) |
| 4 | "whose xz projection is an immersion of the parameter circle" (3331-3332) | `projection` | `K.front.loop.γ t = ((K.T t).1, (K.T t).2.2)` (a `SmoothLoop`), `K.front.vel t = (x′ t, z′ t)`, `K.front.vel t ≠ 0` |
| 5 | "with finitely many transverse double points" (3332-3333) | `double_points` | `doubleSet` = the ordered pairs of distinct parameters of `[0,1)` with equal projection (a `Finset`); `IsDouble s t → det (vel s) (vel t) ≠ 0` |
| 6 | "and no triple point" (3333-3334) | `no_triple` | three pairwise distinct points of the circle never share a projection |
| 7 | "the over strand at each double point being the branch of smaller y" (3334-3335) | `over_rule` | `K.front.isOver s t ↔ K.front.IsDouble s t ∧ yOf K.T s < yOf K.T t`; at every double point exactly one branch is over (`Xor`) |
| 8 | "It has no cusp." (3335) — consequence | `no_cusp` | `K.front.vel t ≠ 0` for all `t` (the accepted cusp criterion `IsCusp ↔ vel = 0` never holds) |
| 9 | "At a vertical tangent, x′ = 0, the inequality gives z′ > 0: every vertical tangent … points upward, a consequence and not a hypothesis." (3335-3338) — consequence | `vertical_up` | `deriv (xOf K.T) t = 0 → 0 < deriv (zOf K.T) t` and `(K.front.vel t).1 = 0 → 0 < (K.front.vel t).2`, PROVED from `positive` (`TransverseKnot.vertical_up`: rewrite x′ = 0 in z′ − y x′ > 0) |
| 10 | "The diagram determines its writhe and its over/under counts" (3338-3339), the quantities | `writhe_counts` | for every `D : SmoothKnotDiagram`: `writhe = ∑ q ∈ crossingPairs, crossSign q.1 q.2`; `crossingPairs` = `doubleSet` filtered by `isOver` (each double point once, `crossingPairs_xor_swap`); `crossSign = sign det(u_O, u_U)` in ℤ; `overCount = crossingCount`, `underCount = crossingCount`; `overOcc ∪ underOcc = occSet`, `Disjoint overOcc underOcc` |
| 11 | same sentence, the determination | `determined` | `K.xz = K'.xz → (y-order agrees at the double points of K) → K.front = K'.front ∧ writhe, overCount, underCount agree` (`front_ext`) |
| 12 | "the knot T is named separately where it is used" (3339-3340) | `knot_named` | `IsGenericPositiveTransverseFront D ↔ ∃ K, K.front = D`; every `K.front` is one; the knot is the separate object `K` |

The class structures behind the bundle, one field per printed clause:
* `TransverseKnot` (§4): `T`, `smooth`, `periodic`, `embedded`, `positive`, `immersion`, `doubles_finite`, `transverse`,
  `no_triple` — clauses 2-6 on the knot.
* `SmoothKnotDiagram` (§3): `loop : SmoothLoop`, `immersion`, `doubles_finite`, `transverse`, `no_triple`,
  `isOver : ℝ → ℝ → Prop`, `isOver_isDouble`, `isOver_xor`, `isOver_congr` — the accepted layer's smooth diagram
  "with over/under choices at its transverse double points" (sm-3:341-343, def:gauss-record 353-356), one component.
* `TransverseKnot.front : SmoothKnotDiagram` — `loop := K.xz` (the xz projection, literally a `SmoothLoop`),
  `isOver := K.IsOver` (= `IsDouble ∧ y s < y t`).
* `IsGenericPositiveTransverseFront D := ∃ K : TransverseKnot, K.front = D`.

## 3. Design decisions (the six points of the brief)

1. **The space curve.** `T : ℝ → Space` with `Space = ℝ × ℝ × ℝ`, `ContDiff ℝ ∞ T`, `Function.Periodic T 1` (a
   parameter circle as in `SmoothLoop`, FR-3).  Coordinates are the functions `xOf T, yOf T, zOf T` and the projection
   `xzOf T t = (xOf T t, zOf T t)`, so `K.xz : SmoothLoop` is literally `⟨xzOf K.T, smooth_xz, periodic_xz⟩` and the
   front's velocity is `(x′, z′)` (`deriv_xz`, via `HasDerivAt.prodMk`).  `EuclideanSpace ℝ (Fin 3)` was not used: the
   accepted `Plane` is `ℝ × ℝ`, and the product form gives the projection by `rfl`.  Embedded = injective on the circle
   (`embedded : T s = T t → SameT s t`); "oriented" = the parameter direction (reading T-1).  Positivity is stated in
   the printed coordinates `0 < z′ − y x′` and shown equal to `contactForm (T t) (deriv T t)` (`positive_contactForm`,
   `deriv_T : deriv T t = (x′, y′, z′)`).  The immersion of the projection is a printed clause and is kept as the field
   `immersion`, although positivity implies it (`vel_ne_zero_of_positive`; risk R-1); the immersion of `T` itself is
   derived (`deriv_T_ne_zero`).  Finiteness, transversality, no triple point are stated on the projection exactly as in
   the accepted `SmoothFront` (ordered pairs in `[0,1)²`, `det ≠ 0`, three-point clause), with the one-circle relation
   `SameT s t := ∃ n : ℤ, t = s + n` (`SameT.sameParam_iff` identifies it with `SameParam` on `Fin 1`).
2. **The front.** `K.front : SmoothKnotDiagram` = the projection with the over relation `IsOver s t := IsDouble s t ∧
   y s < y t`.  At a double point the y-values differ because `T` is embedded (`y_ne_of_isDouble`), so exactly one
   branch is over (`front.isOver_xor`); the relation is invariant under the period (`isOver_congr`).  The over/under
   datum is a relation on parameters rather than a `Bool` on a finite type so that the diagram is an ordinary structure
   with an extensionality principle (`SmoothKnotDiagram.ext'`: a diagram is its curve with its choices).
3. **"It has no cusp."** The projection cannot be viewed in `SmoothFront`: `SmoothFront.no_vertical` forbids vertical
   tangents on regular arcs, and every closed curve has one (`exists_vertical_tangent`, Rolle `exists_deriv_eq_zero` on
   the periodic `x`), where the transverse front is regular — so `SmoothFront.comp_ne_xz : F.comp i ≠ K.xz` for every
   `F, i` (this is the same fact as the accepted `SmoothFront.not_cuspFree`, seen from the other side).  Hence the
   clause is stated as `K.front.vel t ≠ 0` (`deriv ≠ 0`), which is exactly the negation of the accepted cusp criterion
   `IsCusp p ↔ vel p = 0`; and the front lives in the plain-loop vocabulary of SM/FrontRecordBridge §2, with bridges
   `loops : Fin 1 → SmoothLoop`, `isDoubleOf_loops`, `crossSignOf_loops`, `slopeOf_loops`, `mem_occSetOf_loops`.
4. **Vertical tangents point upward.** PROVED: `TransverseKnot.vertical_up (h : deriv (xOf K.T) t = 0) : 0 < deriv (zOf
   K.T) t` (substitute in `positive`), and `front_vertical_up` in the front's vocabulary; `exists_vertical_tangent`
   shows the clause is not vacuous.
5. **Writhe and over/under counts.** `writhe D = ∑ q ∈ D.crossingPairs, D.crossSign q.1 q.2` with `crossingPairs =
   doubleSet.filter isOver` (each double point once as `(over, under)`) and `crossSign s t = if 0 < det (vel s) (vel t)
   then 1 else −1` (= `SignType.sign` in ℤ, `crossSign_eq_sign`): the right-hand side of fd:front-writhe with over =
   smaller y.  "Over/under counts" (reading T-4): `overOcc`/`underOcc` = the occurrence parameters at which the strand is
   the over/under branch, `overCount`/`underCount` their cardinalities; proved `overCount = underCount = crossingCount`
   (injectivity of the partner map = "no triple point", `fst_injOn_crossingPairs`, `snd_injOn_crossingPairs`),
   `overOcc ∪ underOcc = occSet`, `Disjoint`, `card occSet = 2 · crossingCount`.  "The diagram determines" (T-5): the
   quantities take a `SmoothKnotDiagram`, never a knot, and `front_ext`/`determined` show the front depends on `T` only
   through its projection and the y-order at the double points — the y-coordinate enters through the over rule alone.
6. **Fidelity risks:** §5 below.

## 4. Readings (T-1..T-5, also in the module header)

* **T-1** smooth = `C^∞`; parameter circle = 1-periodic map of `ℝ` (FR-3); oriented = parameter direction; embedded =
  injective on the circle; the immersion of `T` is derived.
* **T-2** over = smaller y, as a relation `IsDouble ∧ y s < y t` on parameters; well defined by embeddedness.  This is
  the observer rule of fd:contact's proof, distinct from the Legendrian smaller-slope rule of ng:front-domain.
* **T-3** no cusp = `vel ≠ 0` (negated accepted criterion); the front is not a `SmoothFront` (`comp_ne_xz`).
* **T-4** over/under counts = the tallies of the over/under bits along the traversal (def:gauss-record "an over/under
  bit at each occurrence", rem:crossing-record "the over/under bit of each visit"); each equals the crossing number.
  The phrase occurs once in the document (3337); the alternative "numbers of positive/negative crossings" is derivable
  (`crossingPairs.filter (crossSign = ±1)`) but is not the phrase.
* **T-5** determination = definitional (functions of the diagram) + extensionality (`front_ext`).

## 5. Fidelity risks (to be cited by the reviewer of row 92 and by rows 94, 97/cf:thm-carrierfloor)

* **R-1 (redundant printed clause).** `immersion` (projection regular) follows from `positive`
  (`vel_ne_zero_of_positive`); it is kept as a field because it is a printed clause (as the accepted row kept
  `cusps_finite`).  Constructing a `TransverseKnot` therefore asks for one provable hypothesis; harmless.
* **R-2 (orientation).** Orientation is the parameter direction; no orientation-reversal vocabulary is provided.
  Positivity `z′ − y x′ > 0` fixes the traversal direction of a transverse knot (reversal negates it), so a knot has one
  orientation compatible with the class — consistent with "positive transverse".
* **R-3 (polygonal reading not built — GAP-1).** fd:contact's second half needs "T … whose specified xz projection D_T
  is an ordinary finite regular generic diagram" and its polynomial `P_T`; cf:thm-carrierfloor(C) needs "Its front and
  its smaller-y over/under assignments are exactly the diagram T".  Both require a polygonal `Diagram` carrying the
  record of `K.front` with the smaller-y over bits.  The existing polygonal reading `GeomMarking G S` (SM/FrontGeomModel)
  reads over = smaller slope (the Legendrian rule) and therefore does NOT apply to transverse fronts; the needed
  variant is `GeomMarking` with `slopeOf G p < slopeOf G q` replaced by `D.isOver p q` (and the sign clause by
  `D.crossSign`) — a mechanical copy that belongs to the row that consumes it (FR-1: a smooth diagram's polynomial is
  read through a polygonal `Diagram`).  Not built here, per the brief.
* **R-4 (the phrase "over/under counts").** Reading T-4; recorded because the phrase is a one-off.  If the reviewer
  prefers the signed-crossing reading, both counts are `Finset.filter`s of `crossingPairs` and can be added without
  changing any declaration.
* **R-5 (a class the text does not name).** `SmoothKnotDiagram` renders "the oriented knot diagram in the (x,z) plane"
  as the accepted layer's smooth diagram of one oriented circle with over/under choices (sm-3:341-343, def:gauss-record).
  Its `isOver` is an arbitrary choice satisfying three axioms; a transverse front is one whose choice is the smaller-y
  rule of some knot (`IsGenericPositiveTransverseFront`, existential over knots — the front does not carry its knot,
  matching "the knot T is named separately").  The record is read on parameters, not on points (FR-3).
* **R-6 (sl not defined).** Self-linking is not defined in the frozen source (cv-lane-plan §161); this module defines
  none.  src:contact must declare `sl` (∃-form) and fd:contact consume it; see §6.

## 6. What src:contact and fd:contact will need from this module

* The knot and its front: `TransverseKnot` (the "individual smooth positive transverse knot T"), `K.front :
  SmoothKnotDiagram`, `IsGenericPositiveTransverseFront`.
* The writhe formula fd:front-writhe: `K.front.writhe = ∑ q ∈ K.front.crossingPairs, K.front.crossSign q.1 q.2`
  (`writhe_def`), with `q ∈ crossingPairs ↔ q ∈ doubleSet ∧ isOver q.1 q.2` (the over-first pair `(O, U)`),
  `u_O(q) = K.front.vel q.1`, `u_U(q) = K.front.vel q.2`, `crossSign = sign det_xz(u_O, u_U)` (`crossSign_eq_sign`),
  and `front_vel : K.front.vel t = (x′ t, z′ t)` for the proof's `(a, c), (b, d)` tangents.
* "In the xz front page the smaller-y branch is over": `front_isOver : K.front.isOver s t ↔ K.IsDouble s t ∧ y s < y t`.
* A declaration `sl : TransverseKnot → ℤ` (or ℝ via the Gauss linking integral of `T` and its pushoff, fd:framed-linking)
  is to be supplied by src:contact / fd:linking-calculus; `contactForm`, `Space`, `deriv_T`, `hasDerivAt_T`,
  `yOf`/`xOf`/`zOf` are the vocabulary for the pushoff `T + ε ∂_y` and for rows 84-88.
* fd:contact's `D_T` / `P_T`: a smaller-y `GeomMarking` variant on `K.front.loops` (R-3), then `P S` through the
  accepted `presentations`; `loops`, `isDoubleOf_loops`, `crossSignOf_loops`, `mem_occSetOf_loops` connect `K.front`
  to the `Fin c → SmoothLoop` vocabulary those structures are written in.
* fd:contact's proof contrasts the Legendrian front `F_T` (a `SmoothFront`) with the transverse front:
  `SmoothFront.comp_ne_xz` records that the two classes are disjoint, so `w(F_T)` (`SmoothFront.writhe`) and `w(T)`
  (`SmoothKnotDiagram.writhe`) are different functions that the theorem relates through `sl`.

## 7. Summary

```
{ "file": "work/drafts/front/TransverseFront.lean",
  "lines": 914,
  "declarations": 135,
  "main": "SM.transverse_front_definition : SM.TransverseFrontDefinitionData (13 fields)",
  "classes": ["SM.Space", "SM.contactForm", "SM.SameT", "SM.SmoothKnotDiagram", "SM.TransverseKnot",
              "SM.TransverseKnot.front", "SM.IsGenericPositiveTransverseFront"],
  "proved_consequences": ["TransverseKnot.vertical_up", "front_vertical_up", "vel_ne_zero_of_positive",
                          "deriv_T_ne_zero", "exists_vertical_tangent", "SmoothFront.comp_ne_xz",
                          "overCount_eq", "underCount_eq", "overOcc_union_underOcc", "disjoint_overOcc_underOcc",
                          "card_occSet", "front_ext"],
  "compile": "lake env lean ../drafts/front/TransverseFront.lean: 0 errors, 0 warnings, no placeholders",
  "axioms": ["propext", "Classical.choice", "Quot.sound"],
  "readings": ["T-1", "T-2", "T-3", "T-4", "T-5"],
  "risks": ["R-1 immersion redundant (kept)", "R-2 orientation = parameter direction",
            "R-3 smaller-y polygonal reading not built (GAP-1; GeomMarking is smaller-slope)",
            "R-4 over/under counts read as traversal tallies", "R-5 SmoothKnotDiagram is the accepted smooth-diagram class",
            "R-6 sl not defined here"] }
```
