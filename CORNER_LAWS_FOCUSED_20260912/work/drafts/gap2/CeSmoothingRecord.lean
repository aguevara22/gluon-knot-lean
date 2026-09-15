import SM.TransverseFront
import SM.FrontRecordBridge
import SM.FrontGeomModel
import SM.PolynomialBlock

/-! # Row 90 ce:smoothing-record — Scalar independence of clean cusp smoothing

Source: reference/SM/sm-3-statesum.tex:3171-3182 (statement), 3183-3195 (proof); the preceding
lemma ce:rounding (3029-3058) supplies the vocabulary (the spatial link `L`, its cusped projection
`p = (x, z)`, the exact cusp germ, the rounding family `L_λ` with `D_ε = p(L_1)`).  Design memo:
work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "90 ce:smoothing-record", §5; statement sketch:
work/drafts/gap2/Gap2Statements.lean §3-§5.  Main declaration: `SM.ce_smoothing_record :
CeSmoothingRecordData` (§6).  Accepted analogue: ng:smoothing-record, `SM.ng_smoothing_record`
(SM/FrontRecordBridge.lean) and its geometric model (SM/FrontGeomModel.lean).

## The printed statement (sm-3:3173-3180, verbatim)

"For a front satisfying Lemma ce:rounding, define a permitted smoothed-front diagram by replacing
each cusp with one regular embedded oriented arc in a clean cusp neighbourhood, agreeing with the
old germs in endpoint collars and creating no crossing. Retain every double point with its original
height choice. Every such actual diagram has the same named decorated record as the diagram
D_ε = p(L_1) of the lemma, including crossing-free components. Consequently their source values
F_D(l,m) and campaign polynomials P_D(a,z) agree."

## The printed proof (sm-3:3184-3194, verbatim)

"A cusp replacement introduces no crossing visit and changes no successor of an old visit along
the oriented parameter circle. All crossing pairings, signs and O/U bits remain unchanged because
their germs lie outside the cusp neighbourhoods. The component correspondence is the identity on
the original circles, including those without crossings. Thus the two actual diagrams have a named
decorated-record isomorphism. Lemma rp:record-polynomial, with the same source construction of
Literature input lp:lm, gives equality of F_D; the common substitution of Theorem lp:core preserves
it. This is a scalar statement, not a classification of arbitrary relative arc embeddings or an
ambient completeness assertion."

## Printed clause → field of `CeSmoothingRecordData`

| tex lines | printed | field |
|---|---|---|
| 3173 | "For a front satisfying Lemma ce:rounding" | the prefix of every field: `L : SpatialLink c`, `0 < c`, `L.CuspedProjection` (the lemma's hypotheses; `0 < c` is not used by any proof) |
| 3173-3175 | "define a permitted smoothed-front diagram by replacing each cusp with one regular embedded oriented arc" | `smoothing_arc` |
| 3175 | "in a clean cusp neighbourhood" | `clean_neighbourhood` |
| 3175-3176 | "agreeing with the old germs in endpoint collars" | `endpoint_collars` |
| 3176 | "and creating no crossing" | `no_crossing` (with the consequence: no new double point) |
| 3176-3177 | "Retain every double point with its original height choice." | `height_choice` |
| 3177-3178 | "Every such actual diagram has the same named decorated record as the diagram D_ε = p(L_1) of the lemma" | `same_record_as_endpoint` |
| 3179 | "including crossing-free components" | `crossing_free_components` |
| 3179-3180 | "Consequently their source values F_D(l,m) and campaign polynomials P_D(a,z) agree." | `source_and_polynomial` (consequence) |

The printed proof's "Thus the two actual diagrams have a named decorated-record isomorphism" (any
two permitted diagrams) is the module theorem `SpatialLink.recordIso_nonempty_of_cleanCuspSmoothings`
(§4), with `lmF_eq_of_cleanCuspSmoothings`, `P_eq_of_cleanCuspSmoothings`; the bundle carries only
the clauses of the printed STATEMENT (the trimming rule of the accepted SM/FrontRecordBridge.lean).

## Vocabulary (§1) — the sketch's §3, copied, with ONE change

`SpatialLink c` ("a smooth oriented spatial embedding of a finite union of parameter circles in
ℝ³"), `projLoop` (the `xz` projection, a `SmoothLoop`), `height` (the `y` coordinate), `IsCusp`,
`cuspSet`, `ExactCuspGerm`, `CuspedProjection` (the hypotheses of ce:rounding), `RegularGenericProjection`,
`HeightMarking L G S` (FR-1 with the height over-rule: the polygonal `Diagram S` carries the named
record of the loops `G`, over = smaller `y` of `L`), `CleanCuspSmoothing L G` (the permitted
smoothing), `SpatialFamily`, `CuspRoundingFamily L` (the conclusion of ce:rounding as a structure;
its `clean` field refers to the `CleanCuspSmoothing` of this file).

Change D-1 (recorded): `CleanCuspSmoothing.collar` is NEW.  The printed definition says the new
arc agrees "with the old germs in endpoint collars"; the sketch rendered this by `agree` alone
(equality with the projection at every parameter whose orbit avoids the OPEN arcs, i.e. at the end
points and outside), which does not force the germs at the end points to agree from inside the arc
(a `C^∞` loop may differ from the old arc at every interior point of the arc while matching all
derivatives at its ends).  `collar` asks for a collar `(a k, a k + η) ∪ (b k − η, b k)` on which the
new arc IS the old arc, which together with `agree` gives equality on a neighbourhood of each end
point — the printed germ agreement.  ce:rounding's construction has it (its cutoff `ρ` is supported
strictly inside `(−b, b)`, sm-3:3083-3084, 3105-3106).  No proof of this file uses `collar`.

## Readings (for the reviewer; the report lists them with the risks)

* R-1 "a front satisfying Lemma ce:rounding": the spatial link `L` whose `xz` projection is the
  front; hypotheses `0 < c` and `L.CuspedProjection` as for row 89.  The row is stated on `L`, not
  on the projection alone, because the decoration ("height choice") needs the `y` coordinate.
  "no cusps on another branch" is a consequence of `CuspedProjection.transverse` (a cusp branch has
  zero projected velocity, so the determinant vanishes).
* R-2 "permitted smoothed-front diagram" / "actual diagram": the smoothed curves are a loop family
  `G : Fin c → SmoothLoop` on the SAME parameter circles with `L.CleanCuspSmoothing G` (FR-4:
  parametrized replacement); the diagram is read polygonally (FR-1), as a `Diagram S` carrying the
  named record of `G` with `L`'s heights (`L.HeightMarking G S`).  No smooth `Diagram` exists in
  the accepted layer; existence of a polygonal carrier is not asserted (as in ng:front-domain).
* R-3 "one regular embedded oriented arc": `regular`, `simple` on the open arc `(a k, b k)`;
  "oriented" = traversed in the parameter direction of the same circle (T-1).
* R-4 "clean cusp neighbourhood": the closed disc `U k` (`IsDisc`: convex, compact, nonempty
  interior — the accepted `GeomRounding` reading; convexity is an unprinted restriction inherited
  from it, harmless here: no proof uses `U`), which the projection meets only along the cusp's own
  closed arc (`clean`, `arc_in`, `arc_simple`); the new arc stays inside (`inside`).
* R-5 "Retain every double point with its original height choice": every double point of the
  projection is a double point of the smoothing with the same value and velocity
  (`isDoubleOf_iff`, `eval_eq_of_isDouble`, `deriv_eq_of_isDouble`), and the over bit of the
  reading is `L`'s height order at that double point (`HeightMarking.over_iff`, over = smaller `y`,
  the convention of fd:contact sm-3:3406-3407).
* R-6 "the same named decorated record": `Nonempty (RecordIso S.record X.record)` — the accepted
  `RecordIso` (circles, occurrences, successor, pairing, bits, signs), as in ng:smoothing-record.
* R-7 "the diagram D_ε = p(L_1) of the lemma": for any `R : CuspRoundingFamily L` (a family with
  the properties the lemma asserts — the lemma's THEOREM is not used) the polygonal reading `X` of
  the end `p(R.fam.G 1)` with the end's own heights (`(R.fam.G 1).HeightMarking (R.fam.G 1).projLoop
  X`); `R.same_doubles`/`R.same_data` ("retains every original crossing with its oriented decorated
  data") convert it to a reading with `L`'s heights (`CuspRoundingFamily.endMarking`), and
  `R.clean 1` makes `p(L_1)` a permitted diagram.
* R-8 "including crossing-free components": both diagrams have exactly `c` circles
  (`componentCount = c`) and the isomorphism's circle bijection carries circles of occurrences.
* R-9 "source values F_D(l,m)" = `lmF` (the accepted source function of lp:lm), "campaign
  polynomials P_D(a,z)" = `P`; equality through the accepted `lmF_eq_of_recordIso` and
  `presentations` (rp:record-polynomial), exactly the printed proof's last two sentences.

## Route (≈ the accepted ng:smoothing-record argument, on heights instead of slopes)

§2 transports SM/FrontSmooth.lean §8 to `CleanCuspSmoothing`: a branch of a double point of the
projection is closed-arc-free (`arc_simple`), so the smoothing has the projection's value there
(`agree`) and — closed-arc-freeness being open for finitely many cusps — its velocity; a branch of
a double point of the smoothing lies on no open arc (`no_crossing`), so the smoothing creates no
crossing (`isDoubleOf_iff`); hence the occurrence sets coincide (`occSetOf_eq`) and the signs agree
(`crossSignOf_eq`).  §3: `HeightMarking.ofSmoothing` reads a marking of `G` as a marking of the
projection (the analogue of `Marking.ofGeom`; the over rule is `L`'s on both sides, so only the
occurrence bijection and the signs are transported), and `HeightMarking.recordIso` composes two
markings of ONE loop family into a `RecordIso` (the analogue of `Marking.recordIso`; the case split
on the sign uses `heights_distinct`).  §4 the pairwise theorems; §5 the end `D_ε`; §6 the bundle. -/

namespace SM

open Link SmoothFront Filter Topology
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The spatial vocabulary (work/drafts/gap2/Gap2Statements.lean §3, copied; change D-1) -/

/-- "a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³"
(ce:rounding, sm-3:3031-3032), "a smooth embedding with nonvanishing parameter derivative"
(cp:finite-contact-path); `c ≥ 1` is the consumer's business.  Orientation = the parameter
direction (T-1). -/
structure SpatialLink (c : ℕ) where
  T : Fin c → ℝ → Space
  smooth : ∀ i, ContDiff ℝ ∞ (T i)
  periodic : ∀ i, Function.Periodic (T i) 1
  /-- embedded: injective on the union of the circles -/
  embedded : ∀ (i j : Fin c) (s t : ℝ), T i s = T j t → i = j ∧ SameT s t
  /-- nonvanishing parameter derivative -/
  regular : ∀ i t, deriv (T i) t ≠ 0

namespace SpatialLink

variable {c : ℕ} (L : SpatialLink c)

/-- the `xz` projection of component `i` ("write p = (x,z) for its projection", sm-3:3032-3033),
as a `SmoothLoop` (the plain-loop vocabulary of SM/FrontRecordBridge.lean §2 applies: `IsDoubleOf`,
`occSetOf`, `crossSignOf`) -/
def projLoop (i : Fin c) : SmoothLoop where
  γ := xzOf (L.T i)
  smooth := ((L.smooth i).fst).prodMk ((L.smooth i).snd.snd)
  periodic := fun t => by
    show xzOf (L.T i) (t + 1) = xzOf (L.T i) t
    simp only [xzOf, xOf, zOf, L.periodic i t]

@[simp] theorem projLoop_γ (i : Fin c) : (L.projLoop i).γ = xzOf (L.T i) := rfl

/-- the height (`y` coordinate) of the point of parameter `p` -/
def height (p : Fin c × ℝ) : ℝ := yOf (L.T p.1) p.2

/-- a cusp of the projection: vanishing projected velocity -/
def IsCusp (i : Fin c) (t : ℝ) : Prop := deriv (xzOf (L.T i)) t = 0

/-- the cusps in the fundamental period -/
def cuspSet : Set (Fin c × ℝ) := {p | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L.IsCusp p.1 p.2}

/-- "the exact germ, on a parameter interval with smooth coordinate u = y − y₀:
x = x₀ + A u², y = y₀ + u, z = z₀ + A y₀ u² + (2A/3) u³, A ≠ 0" (ce:exact-germ, sm-3:3037-3042) at
the cusp parameter `t₀` of component `i` -/
def ExactCuspGerm (i : Fin c) (t₀ : ℝ) : Prop :=
  ∃ (A δ : ℝ), A ≠ 0 ∧ 0 < δ ∧
    (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), deriv (yOf (L.T i)) t ≠ 0) ∧
    ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      L.T i t = ((L.T i t₀).1 + A * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2,
        yOf (L.T i) t,
        (L.T i t₀).2.2 + A * yOf (L.T i) t₀ * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2
          + (2 * A / 3) * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 3)

/-- the printed input class of ce:rounding (sm-3:3033-3042): "Its only failures of regularity are
finitely many isolated cusps; all other projected coincidences are finitely many transverse double
points. Assume there are no triple points or cusps on another branch, and the two y heights at every
double point are distinct. At every cusp assume the exact germ."  ("cusps on another branch" are
excluded by `transverse`: a cusp branch has zero projected velocity.) -/
structure CuspedProjection : Prop where
  cusps_finite : L.cuspSet.Finite
  exact_germ : ∀ p ∈ L.cuspSet, L.ExactCuspGerm p.1 p.2
  doubles_finite : (occSetOf L.projLoop).Finite
  transverse : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0
  no_triple : ∀ p q r : Fin c × ℝ, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
    IsDoubleOf L.projLoop p r → False
  heights_distinct : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q

/-- the projection is an "ordinary finite regular generic diagram" (ce:rounding, sm-3:3050): no
cusp at all, and the double-point clauses (used by `CuspRoundingFamily.generic`) -/
structure RegularGenericProjection : Prop where
  regular : ∀ i t, deriv (xzOf (L.T i)) t ≠ 0
  doubles_finite : (occSetOf L.projLoop).Finite
  transverse : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0
  no_triple : ∀ p q r : Fin c × ℝ, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
    IsDoubleOf L.projLoop p r → False
  heights_distinct : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q

/-- FR-1 with the HEIGHT over-rule: the polygonal `Diagram S` carries the named decorated record of
the loop family `G` (the cusp smoothing of `L`'s projection, or that projection itself when it is
regular), with the over bit at each double point read from the heights of `L` ("Retain every double
point with its original height choice", sm-3:3176-3177; "with smaller y over at the unchanged
crossings", cp:finite-contact-path).  Field for field the accepted `GeomMarking`
(SM/FrontGeomModel.lean) with `slopeOf G` replaced by `L.height`. -/
structure HeightMarking (G : Fin c → SmoothLoop) (S : Diagram) where
  /-- the component circles, crossing-free ones included -/
  e : Fin c ≃ Fin S.Γ.c
  /-- the crossing occurrences (the double-point parameters of `G` in the fundamental period) -/
  Φ : OccOf G ≃ S.Γ.Visit
  /-- an occurrence keeps its circle -/
  comp_eq : ∀ p : OccOf G, S.compOf (Φ p) = e p.1.1
  /-- the cyclic order of the occurrences along each oriented circle -/
  between_iff : ∀ p q r : OccOf G, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (Φ p)) (S.visitCoord (Φ q)) (S.visitCoord (Φ r)))
  /-- the pairing of the two occurrences of each double point -/
  pair_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 → Φ q = S.twin (Φ p)
  /-- over = smaller height ("its original height choice") -/
  over_iff : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    (S.overBit (Φ p) = true ↔ L.height p.1 < L.height q.1)
  /-- the signs: the over-first tangent-determinant sign `sgn det_xz(u_O, u_U)` -/
  sgn_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    L.height p.1 < L.height q.1 → ((S.sign (Φ p).1 : ℤ)) = crossSignOf G p.1 q.1

/-- "a permitted smoothed-front diagram: replacing each cusp with one regular embedded oriented arc
in a clean cusp neighbourhood, agreeing with the old germs in endpoint collars and creating no
crossing" (ce:smoothing-record, sm-3:3173-3176); "every clean ordinary cusp smoothing S(F)"
(cp:finite-contact-path).  Field for field the accepted `SmoothFront.GeomRounding`
(SM/FrontSmooth.lean §8) on the cusps of `L`'s projection, PLUS `collar` (change D-1, module
docstring): the new arc coincides with the old one on a collar of each end of its parameter
interval.
* `U k` a disc about the cusp point (`disc`, `center`), the discs pairwise `disjoint`;
* the cusp's arc is the closed parameter interval `[a k, b k]` around the cusp parameter (`a_lt`,
  `lt_b`), shorter than the circle (`len`);
* *clean*: the projection meets `U k` only along that arc (`clean`), which lies in `U k` (`arc_in`)
  and carries no double point (`arc_simple`);
* the smoothing is the projection at every parameter whose orbit `t + ℤ` avoids the open intervals
  `(a k, b k)` of its circle (`agree`: "replacing each cusp" changes nothing else; the same oriented
  attachments), and on collars of the ends of each arc (`collar`: "agreeing with the old germs in
  endpoint collars");
* on `(a k, b k)` the new arc lies in the disc (`inside`), is regular (`regular`), embedded
  (`simple`) and creates no crossing (`no_crossing`). -/
structure CleanCuspSmoothing (G : Fin c → SmoothLoop) where
  U : L.cuspSet → Set Plane
  a : L.cuspSet → ℝ
  b : L.cuspSet → ℝ
  disc : ∀ k, IsDisc (U k)
  center : ∀ k, xzOf (L.T k.1.1) k.1.2 ∈ interior (U k)
  disjoint : ∀ k k', k ≠ k' → Disjoint (U k) (U k')
  a_lt : ∀ k, a k < k.1.2
  lt_b : ∀ k, k.1.2 < b k
  len : ∀ k, b k - a k < 1
  clean : ∀ k (q : Fin c × ℝ), xzOf (L.T q.1) q.2 ∈ U k →
    q.1 = k.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ Set.Icc (a k) (b k)
  arc_in : ∀ k, ∀ t ∈ Set.Icc (a k) (b k), xzOf (L.T k.1.1) t ∈ U k
  arc_simple : ∀ k, ∀ t ∈ Set.Icc (a k) (b k), ∀ q : Fin c × ℝ, ¬ SameParam (k.1.1, t) q →
    xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t
  agree : ∀ (i : Fin c) (t : ℝ),
    (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (a k) (b k)) →
    (G i).γ t = xzOf (L.T i) t
  /-- D-1: "agreeing with the old germs in endpoint collars" -/
  collar : ∀ k, ∃ η : ℝ, 0 < η ∧
    ∀ t ∈ Set.Ioo (a k) (a k + η) ∪ Set.Ioo (b k - η) (b k), (G k.1.1).γ t = xzOf (L.T k.1.1) t
  inside : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), (G k.1.1).γ t ∈ U k
  regular : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), deriv (G k.1.1).γ t ≠ 0
  simple : ∀ k, Set.InjOn (G k.1.1).γ (Set.Ioo (a k) (b k))
  no_crossing : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), ∀ q : Fin c × ℝ, ¬ SameParam (k.1.1, t) q →
    (G q.1).γ q.2 ≠ (G k.1.1).γ t

end SpatialLink

/-- "a jointly smooth family of oriented spatial embeddings" (ce:rounding, sm-3:3047-3048), each
slice a `SpatialLink` (embedded, regular) -/
structure SpatialFamily (c : ℕ) where
  G : ℝ → SpatialLink c
  joint_smooth : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (G p.1).T i p.2)

/-- The conclusion of ce:rounding (sm-3:3047-3054) as a structure (sketch §4): "a jointly smooth
family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L, fixed outside disjoint cusp
parameter intervals, such that for every λ > 0 its xz projection is an ordinary finite regular
generic diagram. It cleanly smooths the cusps, creates no crossing, and retains every original
crossing with its oriented decorated data. All original parameter circles, component labels and
traversal orientations are retained."  Row 90 refers to its end `D_ε = p(L_1)`; the lemma's
theorem (row 89) is NOT used, only this description of its output. -/
structure CuspRoundingFamily {c : ℕ} (L : SpatialLink c) where
  fam : SpatialFamily c
  start : fam.G 0 = L
  /-- the disjoint cusp parameter intervals -/
  a : L.cuspSet → ℝ
  b : L.cuspSet → ℝ
  a_lt : ∀ k, a k < k.1.2
  lt_b : ∀ k, k.1.2 < b k
  len : ∀ k, b k - a k < 1
  intervals_disjoint : ∀ k k', k ≠ k' → k.1.1 = k'.1.1 →
    Disjoint (Set.Ioo (a k) (b k)) (Set.Ioo (a k') (b k'))
  /-- fixed outside the cusp intervals (same circles, labels, orientations: the parameter is kept) -/
  fixed_outside : ∀ (lam : ℝ) (i : Fin c) (t : ℝ),
    (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (a k) (b k)) →
    (fam.G lam).T i t = L.T i t
  /-- for every λ > 0 the projection is an ordinary finite regular generic diagram -/
  generic : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → (fam.G lam).RegularGenericProjection
  /-- the smoothing is clean, in the sense of `CleanCuspSmoothing`, at every λ > 0 -/
  clean : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → Nonempty (L.CleanCuspSmoothing (fam.G lam).projLoop)
  /-- creates no crossing and retains every original crossing … -/
  same_doubles : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ p q : Fin c × ℝ,
    IsDoubleOf (fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q
  /-- … with its oriented decorated data (sign and height order) -/
  same_data : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    crossSignOf (fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
    ((fam.G lam).height p < (fam.G lam).height q ↔ L.height p < L.height q)

/-! ## 2. A clean cusp smoothing keeps the double points, values and velocities of the projection

SM/FrontSmooth.lean §8 (`GeomRounding.isDouble_iff`, `deriv_eq_of_isDouble`) transported from a
front `F` with `F.comp i` and `F.Cusp` to a spatial link `L` with `L.projLoop i` and `L.cuspSet`;
finiteness of the cusps (a field of `SmoothFront`) is here the hypothesis `L.cuspSet.Finite` of
`CuspedProjection`. -/

namespace SpatialLink

variable {c : ℕ}

/-- periodicity of the projection along the orbit `t + ℤ` -/
theorem xz_add_int (L : SpatialLink c) (i : Fin c) (n : ℤ) (t : ℝ) :
    xzOf (L.T i) (t + n) = xzOf (L.T i) t :=
  (L.projLoop i).eq_add_int n t

/-- the projection takes the same value at two names of one point -/
theorem xz_eq_of_sameParam (L : SpatialLink c) {p q : Param c} (h : SameParam p q) :
    xzOf (L.T q.1) q.2 = xzOf (L.T p.1) p.2 := by
  obtain ⟨h1, n, hn⟩ := h
  rw [← h1, hn]
  exact L.xz_add_int p.1 n p.2

theorem isDoubleOf_projLoop_iff (L : SpatialLink c) (p q : Param c) :
    IsDoubleOf L.projLoop p q ↔
      ¬ SameParam p q ∧ xzOf (L.T p.1) p.2 = xzOf (L.T q.1) q.2 := Iff.rfl

namespace CleanCuspSmoothing

variable {L : SpatialLink c} {G : Fin c → SmoothLoop} (r : L.CleanCuspSmoothing G)
include r

theorem a_lt_b (k : L.cuspSet) : r.a k < r.b k := (r.a_lt k).trans (r.lt_b k)

theorem cusp_mem_Ioo (k : L.cuspSet) : k.1.2 ∈ Set.Ioo (r.a k) (r.b k) := ⟨r.a_lt k, r.lt_b k⟩

/-- "replacing each cusp" changes nothing else: the smoothing is the projection at every parameter
whose orbit avoids the (open) replaced arcs of its circle -/
theorem eval_eq_of_notMem {i : Fin c} {t : ℝ}
    (h : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (r.a k) (r.b k)) :
    (G i).γ t = xzOf (L.T i) t :=
  r.agree i t h

/-- the orbit of the parameter avoids the *closed* replaced arcs of its circle -/
def ClosedArcFree (i : Fin c) (t : ℝ) : Prop :=
  ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Icc (r.a k) (r.b k)

theorem ClosedArcFree.eval_eq {i : Fin c} {t : ℝ} (h : r.ClosedArcFree i t) :
    (G i).γ t = xzOf (L.T i) t :=
  r.agree i t fun k hk n hn => h k hk n (Set.Ioo_subset_Icc_self hn)

/-- closed-arc-freeness is an open condition (finitely many cusps, closed arcs) -/
theorem isOpen_closedArcFree (hfin : L.cuspSet.Finite) (i : Fin c) :
    IsOpen {t : ℝ | r.ClosedArcFree i t} := by
  have : Finite L.cuspSet := hfin.to_subtype
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  show ∀ᶠ (t : ℝ) in nhds t₀, ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Icc (r.a k) (r.b k)
  rw [Filter.eventually_all]
  intro k
  by_cases hk : k.1.1 = i
  · exact (eventually_add_int_notMem_Icc (r.a_lt_b k).le (ht₀ k hk)).mono fun t ht _ => ht
  · exact Filter.Eventually.of_forall fun t hk' => absurd hk' hk

/-- at a closed-arc-free parameter the germ of the smoothing is the germ of the projection
("their germs lie outside the cusp neighbourhoods") -/
theorem eventuallyEq_of_closedArcFree (hfin : L.cuspSet.Finite) {i : Fin c} {t₀ : ℝ}
    (h : r.ClosedArcFree i t₀) : (G i).γ =ᶠ[nhds t₀] xzOf (L.T i) :=
  Filter.eventually_of_mem ((r.isOpen_closedArcFree hfin i).mem_nhds h) fun _ ht =>
    ClosedArcFree.eval_eq r ht

theorem deriv_eq_of_closedArcFree (hfin : L.cuspSet.Finite) {i : Fin c} {t₀ : ℝ}
    (h : r.ClosedArcFree i t₀) : deriv (G i).γ t₀ = deriv (xzOf (L.T i)) t₀ :=
  (r.eventuallyEq_of_closedArcFree hfin h).deriv_eq

/-- a branch of a double point of the projection has no translate on any closed arc: the
projection meets the neighbourhoods only along the simple cusp arcs (`arc_simple`) -/
theorem closedArcFree_of_isDouble {p q : Param c} (h : IsDoubleOf L.projLoop p q) :
    r.ClosedArcFree p.1 p.2 := by
  intro k hk n hn
  have hsp : SameParam p (k.1.1, p.2 + n) := ⟨hk.symm, n, rfl⟩
  have hs : ¬ SameParam (k.1.1, p.2 + n) q := fun h' => h.1 (hsp.trans h')
  apply r.arc_simple k (p.2 + n) hn q hs
  have he : xzOf (L.T p.1) p.2 = xzOf (L.T q.1) q.2 := h.2
  rw [← he]
  exact (L.xz_eq_of_sameParam hsp).symm

/-- "Retain every double point": the smoothing is the projection at every double point of the
projection -/
theorem eval_eq_of_isDouble {p q : Param c} (h : IsDoubleOf L.projLoop p q) :
    (G p.1).γ p.2 = xzOf (L.T p.1) p.2 :=
  (r.closedArcFree_of_isDouble h).eval_eq

/-- with the projection's velocity -/
theorem deriv_eq_of_isDouble (hfin : L.cuspSet.Finite) {p q : Param c}
    (h : IsDoubleOf L.projLoop p q) :
    deriv (G p.1).γ p.2 = deriv (xzOf (L.T p.1)) p.2 :=
  r.deriv_eq_of_closedArcFree hfin (r.closedArcFree_of_isDouble h)

/-- "creating no crossing": a branch of a double point of the smoothing has no translate on any
open arc -/
theorem notMem_Ioo_of_double {p q : Param c} (hpq : ¬ SameParam p q)
    (he : (G p.1).γ p.2 = (G q.1).γ q.2) :
    ∀ k : L.cuspSet, k.1.1 = p.1 → ∀ n : ℤ, p.2 + n ∉ Set.Ioo (r.a k) (r.b k) := by
  intro k hk n hn
  have hsp : SameParam p (k.1.1, p.2 + n) := ⟨hk.symm, n, rfl⟩
  have hs : ¬ SameParam (k.1.1, p.2 + n) q := fun h => hpq (hsp.trans h)
  apply r.no_crossing k (p.2 + n) hn q hs
  rw [← he, hk, (G p.1).eq_add_int n p.2]

/-- "A cusp replacement introduces no crossing visit" and retains every double point: the double
points of the smoothing, as pairs of parameters of the shared circles, are exactly the double
points of the projection -/
theorem isDoubleOf_iff (p q : Param c) : IsDoubleOf G p q ↔ IsDoubleOf L.projLoop p q := by
  constructor
  · rintro ⟨hpq, he⟩
    refine ⟨hpq, ?_⟩
    have hp : (G p.1).γ p.2 = xzOf (L.T p.1) p.2 :=
      r.agree p.1 p.2 (r.notMem_Ioo_of_double hpq he)
    have hq : (G q.1).γ q.2 = xzOf (L.T q.1) q.2 :=
      r.agree q.1 q.2 (r.notMem_Ioo_of_double (fun h => hpq h.symm) he.symm)
    show xzOf (L.T p.1) p.2 = xzOf (L.T q.1) q.2
    rw [← hp, ← hq]
    exact he
  · intro h
    refine ⟨h.1, ?_⟩
    rw [r.eval_eq_of_isDouble h, r.eval_eq_of_isDouble h.symm]
    exact h.2

/-- "changes no successor of an old visit along the oriented parameter circle": the crossing
occurrences of the smoothing are those of the projection, as the same parameters of the same
oriented circles — so the cyclic order of the occurrences on each circle is literally unchanged -/
theorem occSetOf_eq : occSetOf G = occSetOf L.projLoop := by
  ext p
  simp only [mem_occSetOf]
  constructor
  · rintro ⟨hp, q, hq, hne, he⟩
    have hd : IsDoubleOf G p q := ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp hq hs), he⟩
    exact ⟨hp, q, hq, hne, ((r.isDoubleOf_iff p q).mp hd).2⟩
  · rintro ⟨hp, q, hq, hne, he⟩
    have hd : IsDoubleOf L.projLoop p q :=
      ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp hq hs), he⟩
    exact ⟨hp, q, hq, hne, ((r.isDoubleOf_iff p q).mpr hd).2⟩

/-- "All crossing pairings, signs and O/U bits remain unchanged because their germs lie outside the
cusp neighbourhoods": the over-first tangent-determinant sign of the smoothing at a double point is
the projection's -/
theorem crossSignOf_eq (hfin : L.cuspSet.Finite) {p q : Param c}
    (h : IsDoubleOf L.projLoop p q) : crossSignOf G p q = crossSignOf L.projLoop p q := by
  have hp : deriv (G p.1).γ p.2 = deriv (L.projLoop p.1).γ p.2 := r.deriv_eq_of_isDouble hfin h
  have hq : deriv (G q.1).γ q.2 = deriv (L.projLoop q.1).γ q.2 :=
    r.deriv_eq_of_isDouble hfin h.symm
  unfold crossSignOf
  rw [hp, hq]

/-- the occurrences of the smoothing *are* the occurrences of the projection, as the same
parameters of the same oriented circles -/
def occEquiv : OccOf G ≃ OccOf L.projLoop := Equiv.setCongr r.occSetOf_eq

@[simp] theorem occEquiv_apply_val (p : OccOf G) : (r.occEquiv p).1 = p.1 := rfl

@[simp] theorem occEquiv_symm_apply_val (p : OccOf L.projLoop) : (r.occEquiv.symm p).1 = p.1 :=
  rfl

/-- two distinct parameters meet under the smoothing iff they meet under the projection -/
theorem eval_eq_iff {p q : Param c} (h : ¬ SameParam p q) :
    (G p.1).γ p.2 = (G q.1).γ q.2 ↔ xzOf (L.T p.1) p.2 = xzOf (L.T q.1) q.2 :=
  ⟨fun he => ((r.isDoubleOf_iff p q).mp ⟨h, he⟩).2,
    fun he => ((r.isDoubleOf_iff p q).mpr ⟨h, he⟩).2⟩

end CleanCuspSmoothing

end SpatialLink

/-! ## 3. Height markings: partners, transport along a smoothing, composition -/

namespace SmoothFront

/-- every crossing occurrence of a loop family has a partner: the other branch of its double point -/
theorem OccOf.exists_partner {c : ℕ} {G : Fin c → SmoothLoop} (p : OccOf G) :
    ∃ q : OccOf G, p ≠ q ∧ (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 := by
  obtain ⟨hp, q, hq, hne, he⟩ := mem_occSetOf.mp p.2
  exact ⟨⟨q, mem_occSetOf.mpr ⟨hq, p.1, hp, hne.symm, he.symm⟩⟩,
    fun h => hne (congrArg Subtype.val h), he⟩

end SmoothFront

namespace SpatialLink

namespace HeightMarking

variable {c : ℕ} {L : SpatialLink c} {G : Fin c → SmoothLoop} {S S' : Diagram}

/-- a diagram carrying the record has `L`'s number of circles ("including crossing-free
components") -/
theorem c_eq (m : L.HeightMarking G S) : S.Γ.c = c := (Fin.equiv_iff_eq.mp ⟨m.e⟩).symm

theorem componentCount_eq (m : L.HeightMarking G S) : S.componentCount = c := m.c_eq

/-- the occurrence sent to the twin of `Φ p` is the partner of `p` -/
theorem partner_of_Φ_eq_twin (m : L.HeightMarking G S) {p q : OccOf G}
    (h : m.Φ q = S.twin (m.Φ p)) : p ≠ q ∧ (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 := by
  obtain ⟨q₀, hne, he⟩ := OccOf.exists_partner p
  have hq : q₀ = q := m.Φ.injective ((m.pair_eq p q₀ hne he).trans h.symm)
  subst hq
  exact ⟨hne, he⟩

theorem compOf_eq_e (m : L.HeightMarking G S) (v : S.Γ.Visit) :
    S.compOf v = m.e (m.Φ.symm v).1.1 := by
  have h := m.comp_eq (m.Φ.symm v)
  rwa [Equiv.apply_symm_apply] at h

theorem compOf_eq_iff (m : L.HeightMarking G S) (v w : S.Γ.Visit) :
    S.compOf v = S.compOf w ↔ (m.Φ.symm v).1.1 = (m.Φ.symm w).1.1 := by
  rw [m.compOf_eq_e v, m.compOf_eq_e w, m.e.apply_eq_iff_eq]

/-- the cyclic order of three occurrences of one circle, read on the parameters -/
theorem visitBetween_iff (m : L.HeightMarking G S) {p q s : OccOf G} (hpq : p.1.1 = q.1.1)
    (hqs : q.1.1 = s.1.1) :
    S.VisitBetween (m.Φ p) (m.Φ q) (m.Φ s) ↔ cycBetween p.1.2 q.1.2 s.1.2 :=
  (m.between_iff p q s hpq hqs).symm

/-- **Transport along a clean cusp smoothing** (the analogue of the accepted `Marking.ofGeom`).
A polygonal diagram carrying the named record of the smoothed curves `G` with `L`'s heights carries
the named record of the projection `p(L)` with `L`'s heights: the occurrences are the same
parameters on the same oriented circles (`occEquiv`, from `occSetOf_eq`: "changes no successor of
an old visit"), so circles and cyclic orders need no argument; meeting is transported by
`eval_eq_iff` ("introduces no crossing visit"); the over rule is `L`'s height order on both sides
("its original height choice") and needs no argument; the signs are transported by
`crossSignOf_eq` ("their germs lie outside the cusp neighbourhoods"). -/
def ofSmoothing (hfin : L.cuspSet.Finite) (r : L.CleanCuspSmoothing G) (m : L.HeightMarking G S) :
    L.HeightMarking L.projLoop S where
  e := m.e
  Φ := r.occEquiv.symm.trans m.Φ
  comp_eq p := m.comp_eq (r.occEquiv.symm p)
  between_iff p q s hpq hqs :=
    m.between_iff (r.occEquiv.symm p) (r.occEquiv.symm q) (r.occEquiv.symm s) hpq hqs
  pair_eq p q hne he :=
    m.pair_eq (r.occEquiv.symm p) (r.occEquiv.symm q)
      (fun h => hne (r.occEquiv.symm.injective h))
      ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mpr he)
  over_iff p q hne he :=
    m.over_iff (r.occEquiv.symm p) (r.occEquiv.symm q)
      (fun h => hne (r.occEquiv.symm.injective h))
      ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mpr he)
  sgn_eq p q hne he hs := by
    have hd : IsDoubleOf L.projLoop p.1 q.1 := OccOf.isDoubleOf_of_ne hne he
    have h : ((S.sign (m.Φ (r.occEquiv.symm p)).1 : ℤ)) = crossSignOf G p.1 q.1 :=
      m.sgn_eq (r.occEquiv.symm p) (r.occEquiv.symm q)
        (fun h => hne (r.occEquiv.symm.injective h))
        ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mpr he) hs
    rw [r.crossSignOf_eq hfin hd] at h
    exact h

@[simp] theorem ofSmoothing_e (hfin : L.cuspSet.Finite) (r : L.CleanCuspSmoothing G)
    (m : L.HeightMarking G S) : (ofSmoothing hfin r m).e = m.e := rfl

@[simp] theorem ofSmoothing_Φ (hfin : L.cuspSet.Finite) (r : L.CleanCuspSmoothing G)
    (m : L.HeightMarking G S) (p : OccOf L.projLoop) :
    (ofSmoothing hfin r m).Φ p = m.Φ (r.occEquiv.symm p) := rfl

/-- **Composition** (the analogue of the accepted `Marking.recordIso`).  Two polygonal readings of
the named record of ONE loop family `G` with `L`'s heights are isomorphic named records (the
accepted `RecordIso`: circles, occurrences, successor, pairing, bits, signs), provided the heights
are distinct at every double point (the case split on which branch is over): "Thus the two actual
diagrams have a named decorated-record isomorphism." -/
def recordIso (hd : ∀ p q : Param c, IsDoubleOf G p q → L.height p ≠ L.height q)
    (m : L.HeightMarking G S) (m' : L.HeightMarking G S') : RecordIso S.record S'.record where
  e := m.e.symm.trans m'.e
  Φ := m.Φ.symm.trans m'.Φ
  comp_eq v := by
    show S'.compOf (m'.Φ (m.Φ.symm v)) = m'.e (m.e.symm (S.compOf v))
    rw [m'.comp_eq, m.compOf_eq_e v, Equiv.symm_apply_apply]
  succ_eq v := by
    show (m.Φ.symm.trans m'.Φ) (S.nextVisit v) = S'.nextVisit ((m.Φ.symm.trans m'.Φ) v)
    apply S.nextVisit_comm_of_visitBetween_iff (m.Φ.symm.trans m'.Φ)
    · intro v w
      show S'.compOf (m'.Φ (m.Φ.symm v)) = S'.compOf (m'.Φ (m.Φ.symm w)) ↔ _
      rw [m'.comp_eq, m'.comp_eq, m'.e.apply_eq_iff_eq, m.compOf_eq_iff]
    · intro v w u hw hu
      rw [m.compOf_eq_iff] at hw hu
      show S'.VisitBetween (m'.Φ (m.Φ.symm v)) (m'.Φ (m.Φ.symm w)) (m'.Φ (m.Φ.symm u)) ↔ _
      rw [m'.visitBetween_iff hw.symm (hw.trans hu.symm)]
      have h := m.visitBetween_iff (p := m.Φ.symm v) (q := m.Φ.symm w) (s := m.Φ.symm u)
        hw.symm (hw.trans hu.symm)
      simp only [Equiv.apply_symm_apply] at h
      exact h.symm
  pair_eq v := by
    show m'.Φ (m.Φ.symm (S.twin v)) = S'.twin (m'.Φ (m.Φ.symm v))
    have hΦ : m.Φ (m.Φ.symm (S.twin v)) = S.twin (m.Φ (m.Φ.symm v)) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨hne, he⟩ := m.partner_of_Φ_eq_twin hΦ
    exact m'.pair_eq _ _ hne he
  bit_eq v := by
    show S'.overBit (m'.Φ (m.Φ.symm v)) = S.overBit v
    obtain ⟨q, hne, he⟩ := OccOf.exists_partner (m.Φ.symm v)
    have h1 := m.over_iff _ q hne he
    have h2 := m'.over_iff _ q hne he
    rw [Equiv.apply_symm_apply] at h1
    exact Bool.eq_iff_iff.mpr (h2.trans h1.symm)
  sgn_eq v := by
    show S'.sign (m'.Φ (m.Φ.symm v)).1 = S.sign v.1
    set p := m.Φ.symm v with hp
    obtain ⟨q, hne, he⟩ := OccOf.exists_partner p
    have hv : m.Φ p = v := Equiv.apply_symm_apply _ _
    have hd' : L.height p.1 ≠ L.height q.1 := hd p.1 q.1 (OccOf.isDoubleOf_of_ne hne he)
    apply signType_intCast_injective
    rcases lt_or_gt_of_ne hd' with hs | hs
    · have h1 := m.sgn_eq p q hne he hs
      have h2 := m'.sgn_eq p q hne he hs
      rw [hv] at h1
      exact h2.trans h1.symm
    · have h1 := m.sgn_eq q p hne.symm he.symm hs
      have h2 := m'.sgn_eq q p hne.symm he.symm hs
      have e1 : (m.Φ q).1 = v.1 := by rw [m.pair_eq p q hne he, S.twin_fst, hv]
      have e2 : (m'.Φ q).1 = (m'.Φ p).1 := by rw [m'.pair_eq p q hne he, S'.twin_fst]
      rw [e1] at h1
      rw [e2] at h2
      exact h2.trans h1.symm

@[simp] theorem recordIso_e (hd : ∀ p q : Param c, IsDoubleOf G p q → L.height p ≠ L.height q)
    (m : L.HeightMarking G S) (m' : L.HeightMarking G S') (i : Fin S.Γ.c) :
    (recordIso hd m m').e i = m'.e (m.e.symm i) := rfl

@[simp] theorem recordIso_Φ (hd : ∀ p q : Param c, IsDoubleOf G p q → L.height p ≠ L.height q)
    (m : L.HeightMarking G S) (m' : L.HeightMarking G S') (v : S.Γ.Visit) :
    (recordIso hd m m').Φ v = m'.Φ (m.Φ.symm v) := rfl

/-- a reading with the heights of another spatial link `L₁` that orders the branches of every
double point of `G` as `L` does is a reading with `L`'s heights (used for `D_ε = p(L_1)`, whose
actual over/under choice is `L_1`'s, "retained" from `L` by ce:rounding) -/
def ofHeightOrder {L₁ : SpatialLink c}
    (hh : ∀ p q : Param c, IsDoubleOf G p q → (L₁.height p < L₁.height q ↔ L.height p < L.height q))
    (m : L₁.HeightMarking G S) : L.HeightMarking G S where
  e := m.e
  Φ := m.Φ
  comp_eq := m.comp_eq
  between_iff := m.between_iff
  pair_eq := m.pair_eq
  over_iff p q hne he :=
    (m.over_iff p q hne he).trans (hh p.1 q.1 (OccOf.isDoubleOf_of_ne hne he))
  sgn_eq p q hne he hs :=
    m.sgn_eq p q hne he ((hh p.1 q.1 (OccOf.isDoubleOf_of_ne hne he)).mpr hs)

end HeightMarking

/-! ## 4. Any two permitted diagrams have the same named record (the printed proof's conclusion) -/

variable {c : ℕ} {L : SpatialLink c}

/-- the named record isomorphism between two permitted smoothed-front diagrams of one spatial link
with cusped projection: transport both readings to the projection (§3) and compose -/
def CleanCuspSmoothing.recordIso (hL : L.CuspedProjection) {G G' : Fin c → SmoothLoop}
    {S S' : Diagram} (r : L.CleanCuspSmoothing G) (r' : L.CleanCuspSmoothing G')
    (m : L.HeightMarking G S) (m' : L.HeightMarking G' S') : RecordIso S.record S'.record :=
  (m.ofSmoothing hL.cusps_finite r).recordIso hL.heights_distinct (m'.ofSmoothing hL.cusps_finite r')

/-- "Thus the two actual diagrams have a named decorated-record isomorphism" (sm-3:3189): any
two permitted smoothed-front diagrams of a spatial link with cusped projection have isomorphic
named records -/
theorem recordIso_nonempty_of_cleanCuspSmoothings (hL : L.CuspedProjection)
    {G G' : Fin c → SmoothLoop} {S S' : Diagram}
    (h : Nonempty (L.CleanCuspSmoothing G)) (h' : Nonempty (L.CleanCuspSmoothing G'))
    (hm : Nonempty (L.HeightMarking G S)) (hm' : Nonempty (L.HeightMarking G' S')) :
    Nonempty (RecordIso S.record S'.record) :=
  h.elim fun r => h'.elim fun r' => hm.elim fun m => hm'.elim fun m' =>
    ⟨r.recordIso hL r' m m'⟩

/-- "Lemma rp:record-polynomial, with the same source construction of Literature input lp:lm, gives
equality of F_D" (sm-3:3190-3191): the accepted `lmF_eq_of_recordIso` -/
theorem lmF_eq_of_cleanCuspSmoothings (hL : L.CuspedProjection)
    {G G' : Fin c → SmoothLoop} {S S' : Diagram}
    (h : Nonempty (L.CleanCuspSmoothing G)) (h' : Nonempty (L.CleanCuspSmoothing G'))
    (hm : Nonempty (L.HeightMarking G S)) (hm' : Nonempty (L.HeightMarking G' S')) :
    lmF S = lmF S' :=
  lmF_eq_of_recordIso S S' (recordIso_nonempty_of_cleanCuspSmoothings hL h h' hm hm')

/-- "the common substitution of Theorem lp:core preserves it" (sm-3:3191-3192): the accepted
`presentations` -/
theorem P_eq_of_cleanCuspSmoothings (hL : L.CuspedProjection)
    {G G' : Fin c → SmoothLoop} {S S' : Diagram}
    (h : Nonempty (L.CleanCuspSmoothing G)) (h' : Nonempty (L.CleanCuspSmoothing G'))
    (hm : Nonempty (L.HeightMarking G S)) (hm' : Nonempty (L.HeightMarking G' S')) :
    P S = P S' :=
  presentations S S' (recordIso_nonempty_of_cleanCuspSmoothings hL h h' hm hm')

end SpatialLink

/-! ## 5. The end `D_ε = p(L_1)` of a rounding family is a permitted diagram -/

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

/-- "It cleanly smooths the cusps": the projection of the end `L_1` is a clean cusp smoothing of
`L`'s projection -/
theorem clean_end : Nonempty (L.CleanCuspSmoothing (R.fam.G 1).projLoop) :=
  R.clean 1 zero_lt_one le_rfl

/-- a chosen clean cusp smoothing structure on `p(L_1)` -/
def endSmoothing : L.CleanCuspSmoothing (R.fam.G 1).projLoop := Classical.choice R.clean_end

/-- "creates no crossing, and retains every original crossing": the double points of `p(L_1)` are
those of `p(L)` -/
theorem same_doubles_end (p q : Param c) :
    IsDoubleOf (R.fam.G 1).projLoop p q ↔ IsDoubleOf L.projLoop p q :=
  R.same_doubles 1 zero_lt_one le_rfl p q

/-- "with its oriented decorated data": the height order of `L_1` at every original double point is
`L`'s -/
theorem height_lt_iff_end {p q : Param c} (h : IsDoubleOf L.projLoop p q) :
    ((R.fam.G 1).height p < (R.fam.G 1).height q ↔ L.height p < L.height q) :=
  (R.same_data 1 zero_lt_one le_rfl p q h).2

/-- the actual diagram `D_ε = p(L_1)` (over = smaller `y` of `L_1`), read polygonally, is a
permitted diagram of `L` (over = smaller `y` of `L`) -/
def endMarking {X : Diagram} (mX : (R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X) :
    L.HeightMarking (R.fam.G 1).projLoop X :=
  SpatialLink.HeightMarking.ofHeightOrder
    (fun p q hd => R.height_lt_iff_end ((R.same_doubles_end p q).mp hd)) mX

/-- the named record isomorphism between a permitted diagram `S` and `D_ε` -/
def recordIsoEnd (hL : L.CuspedProjection) {G : Fin c → SmoothLoop} {S X : Diagram}
    (r : L.CleanCuspSmoothing G) (m : L.HeightMarking G S)
    (mX : (R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X) : RecordIso S.record X.record :=
  r.recordIso hL R.endSmoothing m (R.endMarking mX)

end CuspRoundingFamily

/-! ## 6. The row bundle and theorem -/

open SpatialLink in
/-- Corollary ce:smoothing-record (sm-3:3171-3182), one field per printed clause (the definition
sentence 3173-3176 split at its four sub-clauses, as the accepted `FrontDomainDefinitionData` splits
ng:front-domain's rounding sentence).  Throughout, "a front satisfying Lemma ce:rounding" is a
spatial link `L : SpatialLink c` with `0 < c` and `L.CuspedProjection` (the lemma's hypotheses; `0 <
c` is never used), "a permitted smoothed-front diagram" is a loop family `G` with `r :
L.CleanCuspSmoothing G` read polygonally by `m : L.HeightMarking G S` (FR-1), and "the diagram D_ε =
p(L_1) of the lemma" is the end of a family `R : CuspRoundingFamily L` with the lemma's properties,
read polygonally with `L_1`'s own heights by `mX`. -/
structure CeSmoothingRecordData : Prop where
  /-- sm-3:3173-3175: "define a permitted smoothed-front diagram by replacing each cusp with one
  regular embedded oriented arc": the smoothed curves are `C^∞` 1-periodic loops on the same
  parameter circles, traversed in the parameter direction ("oriented", T-1); the arc replacing the
  cusp `k` is the parameter interval `[a k, b k]` around the cusp parameter, shorter than the
  circle; on its interior the new arc is regular and embedded. -/
  smoothing_arc : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (G : Fin c → SmoothLoop) (r : L.CleanCuspSmoothing G) (k : L.cuspSet),
      (∀ i : Fin c, ContDiff ℝ ∞ (G i).γ ∧ Function.Periodic (G i).γ 1) ∧
      (r.a k < k.1.2 ∧ k.1.2 < r.b k ∧ r.b k - r.a k < 1) ∧
      (∀ t ∈ Set.Ioo (r.a k) (r.b k), deriv (G k.1.1).γ t ≠ 0) ∧
      Set.InjOn (G k.1.1).γ (Set.Ioo (r.a k) (r.b k))
  /-- sm-3:3175: "in a clean cusp neighbourhood": a disc `U k` about the cusp point, the discs
  pairwise disjoint; clean: the projection meets `U k` only along the cusp's own closed arc, which
  lies in `U k` and carries no double point; the new arc stays inside `U k`. -/
  clean_neighbourhood : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (G : Fin c → SmoothLoop) (r : L.CleanCuspSmoothing G) (k : L.cuspSet),
      IsDisc (r.U k) ∧ xzOf (L.T k.1.1) k.1.2 ∈ interior (r.U k) ∧
      (∀ k', k ≠ k' → Disjoint (r.U k) (r.U k')) ∧
      (∀ q : Param c, xzOf (L.T q.1) q.2 ∈ r.U k →
        q.1 = k.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ Set.Icc (r.a k) (r.b k)) ∧
      (∀ t ∈ Set.Icc (r.a k) (r.b k), xzOf (L.T k.1.1) t ∈ r.U k) ∧
      (∀ t ∈ Set.Icc (r.a k) (r.b k), ∀ q : Param c, ¬ SameParam (k.1.1, t) q →
        xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t) ∧
      (∀ t ∈ Set.Ioo (r.a k) (r.b k), (G k.1.1).γ t ∈ r.U k)
  /-- sm-3:3175-3176: "agreeing with the old germs in endpoint collars": on a collar of each end of
  the arc the new arc is the old one (D-1), and outside the open arcs of its circle the smoothing is
  the projection (the replacement changes nothing else). -/
  endpoint_collars : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (G : Fin c → SmoothLoop) (r : L.CleanCuspSmoothing G) (k : L.cuspSet),
      (∃ η : ℝ, 0 < η ∧ ∀ t ∈ Set.Ioo (r.a k) (r.a k + η) ∪ Set.Ioo (r.b k - η) (r.b k),
        (G k.1.1).γ t = xzOf (L.T k.1.1) t) ∧
      ∀ t : ℝ, (∀ k' : L.cuspSet, k'.1.1 = k.1.1 → ∀ n : ℤ, t + n ∉ Set.Ioo (r.a k') (r.b k')) →
        (G k.1.1).γ t = xzOf (L.T k.1.1) t
  /-- sm-3:3176: "and creating no crossing": a point of a replacing arc is met by no other point of
  the smoothed curves; hence (consequence) every double point of the smoothing is a double point of
  the projection. -/
  no_crossing : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (G : Fin c → SmoothLoop) (r : L.CleanCuspSmoothing G),
      (∀ k : L.cuspSet, ∀ t ∈ Set.Ioo (r.a k) (r.b k), ∀ q : Param c, ¬ SameParam (k.1.1, t) q →
        (G q.1).γ q.2 ≠ (G k.1.1).γ t) ∧
      ∀ p q : Param c, IsDoubleOf G p q → IsDoubleOf L.projLoop p q
  /-- sm-3:3176-3177: "Retain every double point with its original height choice.": every double
  point of the projection is a double point of the smoothing, with the projection's value and
  velocity there (consequence of the definition), and in the polygonal reading the over bit at each
  double point is `L`'s height order (over = smaller `y` of `L`). -/
  height_choice : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (G : Fin c → SmoothLoop), L.CleanCuspSmoothing G → ∀ (S : Diagram)
      (m : L.HeightMarking G S),
      (∀ p q : Param c, IsDoubleOf L.projLoop p q →
        IsDoubleOf G p q ∧ (G p.1).γ p.2 = xzOf (L.T p.1) p.2 ∧
          deriv (G p.1).γ p.2 = deriv (xzOf (L.T p.1)) p.2) ∧
      ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
        (S.overBit (m.Φ p) = true ↔ L.height p.1 < L.height q.1)
  /-- sm-3:3177-3178: "Every such actual diagram has the same named decorated record as the diagram
  D_ε = p(L_1) of the lemma": for any family with the lemma's properties, any permitted diagram and
  the polygonal reading of `p(L_1)` (with `L_1`'s heights) have isomorphic named records. -/
  same_record_as_endpoint : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (R : CuspRoundingFamily L) (X : Diagram),
      Nonempty ((R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X) →
    ∀ (G : Fin c → SmoothLoop) (S : Diagram),
      Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.HeightMarking G S) →
      Nonempty (RecordIso S.record X.record)
  /-- sm-3:3179: "including crossing-free components": both diagrams have exactly the `c` circles
  of `L` (crossing-free ones included), and the isomorphism `recordIsoEnd` carries the circle of
  each occurrence to the circle of its image. -/
  crossing_free_components : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → ∀ (hL : L.CuspedProjection)
    (R : CuspRoundingFamily L) (X : Diagram)
    (mX : (R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X)
    (G : Fin c → SmoothLoop) (S : Diagram) (r : L.CleanCuspSmoothing G) (m : L.HeightMarking G S),
      S.componentCount = c ∧ X.componentCount = c ∧
      ∀ v, X.compOf ((R.recordIsoEnd hL r m mX).Φ v) = (R.recordIsoEnd hL r m mX).e (S.compOf v)
  /-- sm-3:3179-3180 (consequence): "Consequently their source values F_D(l,m) and campaign
  polynomials P_D(a,z) agree." -/
  source_and_polynomial : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (R : CuspRoundingFamily L) (X : Diagram),
      Nonempty ((R.fam.G 1).HeightMarking (R.fam.G 1).projLoop X) →
    ∀ (G : Fin c → SmoothLoop) (S : Diagram),
      Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.HeightMarking G S) →
      lmF S = lmF X ∧ P S = P X

open SpatialLink in
/-- **Row 90 ce:smoothing-record.** -/
theorem ce_smoothing_record : CeSmoothingRecordData where
  smoothing_arc := fun _ _ _ G r k =>
    ⟨fun i => ⟨(G i).smooth, (G i).periodic⟩, ⟨r.a_lt k, r.lt_b k, r.len k⟩,
      fun t ht => r.regular k t ht, r.simple k⟩
  clean_neighbourhood := fun _ _ _ _ r k =>
    ⟨r.disc k, r.center k, fun k' h => r.disjoint k k' h, fun q h => r.clean k q h,
      fun t ht => r.arc_in k t ht, fun t ht q h => r.arc_simple k t ht q h,
      fun t ht => r.inside k t ht⟩
  endpoint_collars := fun _ _ _ _ r k => ⟨r.collar k, fun t h => r.agree k.1.1 t h⟩
  no_crossing := fun _ _ _ _ r =>
    ⟨fun k t ht q h => r.no_crossing k t ht q h, fun p q h => (r.isDoubleOf_iff p q).mp h⟩
  height_choice := fun _ _ hL _ r _ m =>
    ⟨fun p q h => ⟨(r.isDoubleOf_iff p q).mpr h, r.eval_eq_of_isDouble h,
        r.deriv_eq_of_isDouble hL.cusps_finite h⟩,
      fun p q hne he => m.over_iff p q hne he⟩
  same_record_as_endpoint := fun _ _ hL R _ hX _ _ hG hS =>
    hX.elim fun mX => hG.elim fun r => hS.elim fun m => ⟨R.recordIsoEnd hL r m mX⟩
  crossing_free_components := fun _ _ hL R _ mX _ _ r m =>
    ⟨m.componentCount_eq, mX.componentCount_eq, fun v => (R.recordIsoEnd hL r m mX).compOf_eq v⟩
  source_and_polynomial := fun _ _ hL R X hX _ S hG hS =>
    have h : Nonempty (RecordIso S.record X.record) :=
      hX.elim fun mX => hG.elim fun r => hS.elim fun m => ⟨R.recordIsoEnd hL r m mX⟩
    ⟨lmF_eq_of_recordIso S X h, presentations S X h⟩

end

end SM
