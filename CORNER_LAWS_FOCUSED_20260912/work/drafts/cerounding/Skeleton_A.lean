import SM.TransverseFront
import SM.Rounding
import SM.FrontRecordBridge
import SM.FrontGeomModel

/-! # SM ce:rounding — ordinary rounding of the exact cusp germs (SKELETON, candidate A)

Source: reference/SM/sm-3-statesum.tex:3029-3058 (statement; the lemma environment closes at 3058),
3059-3170 (proof).  Design memo: work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "89", §5;
statement sketch work/drafts/gap2/Gap2Statements.lean §3-§4 (its vocabulary is reproduced VERBATIM
in §1 below, so that the sibling unit for row 90 ce:smoothing-record and the later row 91 can share
one ported module; the two changes made to the row-89-private structure `CuspRoundingFamily` and the
clause fields added to `CeRoundingData` are listed in §0).  Plan: PLAN_A.md.
SKELETON: §1-§3 are the statement text of Statements_A.lean verbatim; §4 the construction (printed proof
sm-3:3059-3170), §5 the chain of leaf lemmas (sorried), §6 the assembly (proved), §7 the row (proved from the chain).
Check: `cd work/lean && lake env lean ../drafts/cerounding/Skeleton_A.lean`.

## The printed statement (sm-3:3031-3058, clause by clause)

"Let L be a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³,
and write p = (x,z) for its projection. Its only failures of regularity are finitely many isolated
cusps; all other projected coincidences are finitely many transverse double points. Assume there are
no triple points or cusps on another branch, and the two y heights at every double point are
distinct. At every cusp assume the exact germ, on a parameter interval with smooth coordinate
u = y − y₀, [ce:exact-germ] x = x₀ + Au², y = y₀ + u, z = z₀ + Ay₀u² + (2A/3)u³, A ≠ 0. The
coordinate u may increase or decrease along the prescribed component orientation, which is not
changed. The formula is a hypothesis, not an appeal to a classification of singularities.
There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L, fixed
outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
ordinary finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and
retains every original crossing with its oriented decorated data. All original parameter circles,
component labels and traversal orientations are retained. With no cusps take the constant family.
This is an ordinary spatial deformation, not asserted Legendrian or positive transverse, and it
carries no self-linking transport statement."

## Printed notion → Lean (memo §3(d); readings CE-1..CE-9 in PLAN_A.md §2)

| printed | Lean |
|---|---|
| smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³ | `L : SpatialLink c` (`C^∞`, 1-periodic maps `T i : ℝ → Space`, jointly injective on the circles, nonvanishing derivative), `0 < c`; orientation = parameter direction (T-1, FR-3) |
| its projection `p = (x,z)` | `L.projLoop i : SmoothLoop` with `γ = xzOf (L.T i)`; the plain-loop vocabulary `IsDoubleOf`, `occSetOf`, `crossSignOf` (SM/FrontRecordBridge.lean §2) applies |
| failures of regularity = finitely many isolated cusps | `IsCusp i t := deriv (xzOf (L.T i)) t = 0`; `cuspSet.Finite` |
| finitely many transverse double points; no triple points; no cusp on another branch; distinct heights | `CuspedProjection`: `doubles_finite`, `transverse`, `no_triple`, `heights_distinct`; "no cusp on another branch" is a consequence of `transverse` (`CuspedProjection.not_isCusp_of_isDouble`, proved: `det 0 v = 0`) |
| the exact germ on a parameter interval with smooth coordinate `u = y − y₀` | `ExactCuspGerm i t₀`: `∃ A ≠ 0, δ > 0`, `y' ≠ 0` on `(t₀−δ, t₀+δ)` (so `u` is a smooth coordinate, increasing or decreasing), and the three displayed formulas with `u = y t − y t₀` |
| jointly smooth family `L_λ` of oriented spatial embeddings | `SpatialFamily c`: `G : ℝ → SpatialLink c`, `ContDiff ℝ ∞` of the uncurried map on `ℝ × ℝ` |
| `L_0 = L`; fixed outside disjoint cusp parameter intervals | `start`, `a b`, `intervals_disjoint` (disjoint on the circle, i.e. modulo `ℤ`), `fixed_outside` |
| for every `λ > 0` an ordinary finite regular generic diagram | `generic : 0 < λ → λ ≤ 1 → (G λ).RegularGenericProjection` (no cusp, finitely many transverse double points, no triple point, distinct heights — the over rule "smaller y over" is then determined; the polygonal record-carrying `Diagram` is the consumer's FR-1 reading, `HeightMarking`, as for def:transverse-front) |
| cleanly smooths the cusps | `clean : Nonempty (L.CleanCuspSmoothing (G λ).projLoop)` — the definition sentence of ce:smoothing-record, field for field the accepted `GeomRounding` |
| creates no crossing, retains every original crossing with its oriented decorated data | `same_doubles` (the double points, as parameter pairs, are `L`'s), `same_velocity` (the projected velocities at them are `L`'s — the oriented branches), `same_data` (signs and height order) |
| all original parameter circles, component labels and traversal orientations are retained | structural: every slice is a `SpatialLink c` on the same `Fin c` and the same parameter (the family changes only `T`), `fixed_outside` for the values; `same_velocity` for the traversal directions at the crossings |
| with no cusps take the constant family | `CeRoundingData.no_cusps_constant` (a consequence of `fixed_outside`, proved in the bundle assembly) |
| ordinary spatial deformation, not Legendrian/transverse, no self-linking transport | commentary: no field, nothing asserted |

## §0 Changes with respect to the memo sketch (recorded for the 90/91 units)

* `CuspRoundingFamily.intervals_disjoint` is now disjointness ON THE CIRCLE (`∀ n : ℤ`, translates
  by `n`): the memo's version was disjointness of the real intervals only, which allows two arcs of
  one circle to overlap across the period.
* `CuspRoundingFamily.same_velocity` added (projected velocities at the old double points unchanged);
  it implies the memo's sign clause of `same_data`, which is kept verbatim.
* `CeRoundingData` has one field per printed sentence of the conclusion (the accepted pattern of
  `RoundingData`, SM/Rounding.lean §6): `exists_family` carries the theorem, the other fields are the
  readings of the printed sentences on a witness (projections) and the printed "with no cusps take
  the constant family".
* Everything else (`SpatialLink`, `projLoop`, `height`, `IsCusp`, `cuspSet`, `ExactCuspGerm`,
  `CuspedProjection`, `RegularGenericProjection`, `HeightMarking`, `CleanCuspSmoothing`,
  `SpatialFamily`) is byte-identical to Gap2Statements.lean §3. -/

namespace SM

open Link SmoothFront
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The smooth spatial vocabulary (memo §3, verbatim) -/

/-- "a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³"
(ce:rounding), "a smooth embedding with nonvanishing parameter derivative" (cp:finite-contact-path);
`c ≥ 1` is the consumer's business.  Orientation = the parameter direction (T-1). -/
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

/-- the `xz` projection of component `i`, as a `SmoothLoop` (the plain-loop vocabulary of
SM/FrontRecordBridge.lean §2 applies: `IsDoubleOf`, `occSetOf`, `crossSignOf`) -/
def projLoop (i : Fin c) : SmoothLoop where
  γ := xzOf (L.T i)
  smooth := ((L.smooth i).fst).prodMk ((L.smooth i).snd.snd)
  periodic := fun t => by
    show xzOf (L.T i) (t + 1) = xzOf (L.T i) t
    simp only [xzOf, xOf, zOf, L.periodic i t]

/-- the height of the point of parameter `p` -/
def height (p : Fin c × ℝ) : ℝ := yOf (L.T p.1) p.2

/-- a cusp of the projection: vanishing projected velocity -/
def IsCusp (i : Fin c) (t : ℝ) : Prop := deriv (xzOf (L.T i)) t = 0

/-- the cusps in the fundamental period -/
def cuspSet : Set (Fin c × ℝ) := {p | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L.IsCusp p.1 p.2}

/-- "the exact germ, on a parameter interval with smooth coordinate u = y − y₀:
x = x₀ + A u², y = y₀ + u, z = z₀ + A y₀ u² + (2A/3) u³, A ≠ 0" (ce:exact-germ = cp:exact-cusp) at the
cusp parameter `t₀` of component `i` -/
def ExactCuspGerm (i : Fin c) (t₀ : ℝ) : Prop :=
  ∃ (A δ : ℝ), A ≠ 0 ∧ 0 < δ ∧
    (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), deriv (yOf (L.T i)) t ≠ 0) ∧
    ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      L.T i t = ((L.T i t₀).1 + A * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2,
        yOf (L.T i) t,
        (L.T i t₀).2.2 + A * yOf (L.T i) t₀ * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2
          + (2 * A / 3) * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 3)

/-- the printed input class of ce:rounding / cp:finite-contact-path: the projection is regular
except at finitely many cusps, each with the exact germ; the other coincidences are finitely many
transverse double points, none at a cusp, no triple point, distinct heights at every double point -/
structure CuspedProjection : Prop where
  cusps_finite : L.cuspSet.Finite
  exact_germ : ∀ p ∈ L.cuspSet, L.ExactCuspGerm p.1 p.2
  doubles_finite : (occSetOf L.projLoop).Finite
  transverse : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0
  no_triple : ∀ p q r : Fin c × ℝ, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
    IsDoubleOf L.projLoop p r → False
  heights_distinct : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q

/-- the projection is an "ordinary finite regular generic diagram": no cusp at all, and the
double-point clauses (the endpoint `T` of cp:finite-contact-path; every `λ > 0` slice of ce:rounding) -/
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
point with its original height choice"; "with smaller y over at the unchanged crossings").  Field for
field the accepted `GeomMarking` (SM/FrontGeomModel.lean) with `slopeOf G` replaced by `L.height`.
Not used by row 89 itself (the polygonal reading is the consumer's); kept for the shared module. -/
structure HeightMarking (G : Fin c → SmoothLoop) (S : Diagram) where
  e : Fin c ≃ Fin S.Γ.c
  Φ : OccOf G ≃ S.Γ.Visit
  comp_eq : ∀ p : OccOf G, S.compOf (Φ p) = e p.1.1
  between_iff : ∀ p q r : OccOf G, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (Φ p)) (S.visitCoord (Φ q)) (S.visitCoord (Φ r)))
  pair_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 → Φ q = S.twin (Φ p)
  /-- over = smaller height -/
  over_iff : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    (S.overBit (Φ p) = true ↔ L.height p.1 < L.height q.1)
  sgn_eq : ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
    L.height p.1 < L.height q.1 → ((S.sign (Φ p).1 : ℤ)) = crossSignOf G p.1 q.1

/-- "a permitted smoothed-front diagram: replacing each cusp with one regular embedded oriented arc in
a clean cusp neighbourhood, agreeing with the old germs in endpoint collars and creating no crossing"
(ce:smoothing-record); "every clean ordinary cusp smoothing S(F)" (cp:finite-contact-path); "It
cleanly smooths the cusps" (ce:rounding).  Field for field the accepted `SmoothFront.GeomRounding`
(SM/FrontSmooth.lean) on the cusps of `L`'s projection. -/
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
  inside : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), (G k.1.1).γ t ∈ U k
  regular : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), deriv (G k.1.1).γ t ≠ 0
  simple : ∀ k, Set.InjOn (G k.1.1).γ (Set.Ioo (a k) (b k))
  no_crossing : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), ∀ q : Fin c × ℝ, ¬ SameParam (k.1.1, t) q →
    (G q.1).γ q.2 ≠ (G k.1.1).γ t

/-! ### Clause readings proved on the vocabulary -/

/-- two `SpatialLink`s with the same maps are equal (the other fields are proofs) -/
theorem ext' {L L' : SpatialLink c} (h : L.T = L'.T) : L = L' := by
  cases L; cases L'; cases h; rfl

/-- "no … cusps on another branch": a double point never sits at a cusp — a consequence of
`transverse`, since the determinant with a vanishing velocity is `0`. -/
theorem CuspedProjection.not_isCusp_of_isDouble (h : L.CuspedProjection) {p q : Fin c × ℝ}
    (hd : IsDoubleOf L.projLoop p q) : ¬ L.IsCusp p.1 p.2 := by
  intro hc
  apply h.transverse p q hd
  unfold IsCusp at hc
  rw [hc]
  simp [det]

/-- the projection of a component, evaluated: `projLoop` is literally the `xz` projection -/
@[simp] theorem projLoop_γ (i : Fin c) : (L.projLoop i).γ = xzOf (L.T i) := rfl

end SpatialLink

/-- "a jointly smooth family of oriented spatial embeddings" `L_λ` (ce:rounding), `G_t`
(cp:finite-contact-path), each slice a `SpatialLink` (embedded, regular) -/
structure SpatialFamily (c : ℕ) where
  G : ℝ → SpatialLink c
  joint_smooth : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (G p.1).T i p.2)

/-! ## 2. Row 89 ce:rounding: the conclusion as a witness structure, one field per printed clause -/

/-- "There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L,
fixed outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
ordinary finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and
retains every original crossing with its oriented decorated data. All original parameter circles,
component labels and traversal orientations are retained."  The family is indexed by all of `ℝ`
(`SpatialFamily`); the printed clauses concern `0 ≤ λ ≤ 1`, and the slices are the same parameter
circles `Fin c × ℝ/ℤ` (the family changes only the maps `T`). -/
structure CuspRoundingFamily {c : ℕ} (L : SpatialLink c) where
  /-- "a jointly smooth family L_λ … of oriented spatial embeddings" -/
  fam : SpatialFamily c
  /-- "with L_0 = L" -/
  start : fam.G 0 = L
  /-- the left ends of the "disjoint cusp parameter intervals" -/
  a : L.cuspSet → ℝ
  /-- their right ends -/
  b : L.cuspSet → ℝ
  /-- each interval contains its cusp parameter … -/
  a_lt : ∀ k, a k < k.1.2
  lt_b : ∀ k, k.1.2 < b k
  /-- … and is shorter than the circle -/
  len : ∀ k, b k - a k < 1
  /-- "disjoint cusp parameter intervals": on the circle, i.e. no translate of one interval by an
  integer meets another interval of the same component -/
  intervals_disjoint : ∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
    Disjoint (Set.Ioo (a k) (b k)) (Set.Ioo (a k' + n) (b k' + n))
  /-- "fixed outside [the] cusp parameter intervals" (all original parameter circles, component
  labels and traversal orientations are retained: same `Fin c`, same parameter, same values there) -/
  fixed_outside : ∀ (lam : ℝ) (i : Fin c) (t : ℝ),
    (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (a k) (b k)) →
    (fam.G lam).T i t = L.T i t
  /-- "for every λ > 0 its xz projection is an ordinary finite regular generic diagram" -/
  generic : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → (fam.G lam).RegularGenericProjection
  /-- "It cleanly smooths the cusps": every positive slice is a clean cusp smoothing of `L`'s
  projection in the sense of ce:smoothing-record (`CleanCuspSmoothing`) -/
  clean : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → Nonempty (L.CleanCuspSmoothing (fam.G lam).projLoop)
  /-- "creates no crossing, and retains every original crossing": the double points of the
  projection, as pairs of parameters of the shared circles, are exactly those of `L` -/
  same_doubles : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ p q : Fin c × ℝ,
    IsDoubleOf (fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q
  /-- "… with its oriented decorated data": the oriented branches at every original crossing are
  unchanged (the projected velocities are `L`'s) -/
  same_velocity : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    deriv (xzOf ((fam.G lam).T p.1)) p.2 = deriv (xzOf (L.T p.1)) p.2
  /-- "… with its oriented decorated data": crossing sign and height order (over = smaller `y`) -/
  same_data : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    crossSignOf (fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
    ((fam.G lam).height p < (fam.G lam).height q ↔ L.height p < L.height q)

/-! ## 3. The row bundle: one field per printed sentence of the conclusion -/

/-- Lemma ce:rounding (sm-3:3029-3058), one field per printed sentence.  `exists_family` carries the
theorem; the remaining fields are the printed sentences read on a witness (projections of
`CuspRoundingFamily`, in the pattern of the accepted `RoundingData`), plus the printed "With no cusps
take the constant family".  The two closing disclaimers ("an ordinary spatial deformation, not
asserted Legendrian or positive transverse … no self-linking transport statement") assert nothing
and have no field. -/
structure CeRoundingData : Prop where
  /-- "There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L,
  fixed outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
  ordinary finite regular generic diagram …" — for every `L` of the printed input class on a
  nonempty union of circles -/
  exists_family : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    Nonempty (CuspRoundingFamily L)
  /-- "a jointly smooth family L_λ … of oriented spatial embeddings with L_0 = L": joint `C^∞`
  smoothness of the uncurried map, every slice a `SpatialLink` (embedded, regular), start at `L` -/
  smooth_embeddings_start : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingFamily L),
    (∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (W.fam.G p.1).T i p.2)) ∧
    (∀ (lam : ℝ) (i j : Fin c) (s t : ℝ), (W.fam.G lam).T i s = (W.fam.G lam).T j t →
      i = j ∧ SameT s t) ∧
    (∀ (lam : ℝ) (i : Fin c) (t : ℝ), deriv ((W.fam.G lam).T i) t ≠ 0) ∧
    W.fam.G 0 = L
  /-- "fixed outside disjoint cusp parameter intervals" -/
  fixed_outside_disjoint : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingFamily L),
    (∀ k, W.a k < k.1.2 ∧ k.1.2 < W.b k ∧ W.b k - W.a k < 1) ∧
    (∀ k k', k ≠ k' → k.1.1 = k'.1.1 → ∀ n : ℤ,
      Disjoint (Set.Ioo (W.a k) (W.b k)) (Set.Ioo (W.a k' + n) (W.b k' + n))) ∧
    ∀ (lam : ℝ) (i : Fin c) (t : ℝ),
      (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (W.a k) (W.b k)) →
      (W.fam.G lam).T i t = L.T i t
  /-- "such that for every λ > 0 its xz projection is an ordinary finite regular generic diagram" -/
  generic_slices : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingFamily L) (lam : ℝ),
    0 < lam → lam ≤ 1 → (W.fam.G lam).RegularGenericProjection
  /-- "It cleanly smooths the cusps, creates no crossing, and retains every original crossing with
  its oriented decorated data." -/
  clean_no_new_retains : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingFamily L) (lam : ℝ),
    0 < lam → lam ≤ 1 →
    Nonempty (L.CleanCuspSmoothing (W.fam.G lam).projLoop) ∧
    (∀ p q : Fin c × ℝ, IsDoubleOf (W.fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q) ∧
    ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
      deriv (xzOf ((W.fam.G lam).T p.1)) p.2 = deriv (xzOf (L.T p.1)) p.2 ∧
      crossSignOf (W.fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
      ((W.fam.G lam).height p < (W.fam.G lam).height q ↔ L.height p < L.height q)
  /-- "All original parameter circles, component labels and traversal orientations are retained":
  every slice lives on the same `c` parameter circles `ℝ/ℤ` (1-periodic in the same parameter), and
  outside the cusp intervals it is `L` itself -/
  circles_retained : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingFamily L) (lam : ℝ) (i : Fin c),
    Function.Periodic ((W.fam.G lam).T i) 1 ∧
    ∀ t : ℝ, (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (W.a k) (W.b k)) →
      (W.fam.G lam).T i t = L.T i t
  /-- "With no cusps take the constant family": a witness with no cusps is the constant family -/
  no_cusps_constant : ∀ {c : ℕ} (L : SpatialLink c) (W : CuspRoundingFamily L),
    L.cuspSet = ∅ → ∀ lam : ℝ, W.fam.G lam = L


/-! ## 4. The construction (printed proof, sm-3:3059-3170), as explicit definitions

Emphasis of candidate A: maximal reuse of the accepted analytic tools of cf:lem-rounding
(SM/Rounding.lean, Unit P: `Real.smoothTransition` and its profile lemmas; the flatness lemma pattern
`iteratedDeriv_eq_zero_of_const_left`) and of the front block (`GeomRounding`'s consequences, transcribed
to the plain loop families of `CleanCuspSmoothing`).  The cusp rounding of the projection is realised
by the printed displacement (ce:rounding-formula / ce:physical-displacement) and lifted to the spatial
link by the height function `y` (Δy = 0, the height coordinate `u = y − y₀` is the chart coordinate).

* **Cutoff.** The printed `ρ` ("a smooth real cutoff equal to one near zero, with support strictly inside
  `(−b, b)`") is realised in the PARAMETER `t` as the 1-periodic function
  `periodicBump r (t − t₀) = φ((cos 2π(t−t₀) − cos 2πr) / (cos πr − cos 2πr))`, `φ = Real.smoothTransition`:
  smooth and periodic by composition, `= 1` where `dist(t − t₀, ℤ) ≤ r/2`, `= 0` where `dist ≥ r`.  Composed
  with the inverse of the chart coordinate `u` it is a printed `ρ` (even in `u` is not needed).
* **Chart.** `GermData.chart` is ce:positive-chart `X = (x − x₀)/A`, `Z = 3(z − z₀ − y₀(x − x₀))/(2A)`; on the
  chart interval `J = (t₀ − δ, t₀ + δ)` the projection is `(u², u³)` (`chart_proj`).  `δ ≤ 1/3` so that `J`
  embeds in the circle.
* **Clean neighbourhood.** Instead of the printed disc `V` we take, per cusp, the closed rectangle
  `rect = [−M², 2M²] × [u₋³, u₊³]` in normalized coordinates (`u₋ < 0 < u₊` the values of `u` at the two ends
  `a = t₀ − η`, `b = t₀ + η` of the cusp parameter interval, `M = max(|u₋|, u₊)`), pulled back by the affine
  inverse chart: `U = unchart '' rect`, a convex compact set with nonempty interior (`IsDisc`).  The arc
  `[a, b]` fills exactly `U ∩ p(L)` because `Z = u³` is strictly monotone in `u` (no inverse function of `u`
  is needed).  The `remote` constraint (positive distance of the cusp image from the projection of the
  complement of the chart, ce:support-clearance's `d`) is a field of `CuspChoice`, chosen in
  `exists_cuspChoice_within`.
* **Displacement.** `disp μ t = (μ · ε · A · u(t) · χ(t)) • (1, 0, y₀)` = ce:physical-displacement with
  `Δy = 0`; `core μ i t = L.T i t + Σ_{cusps k of circle i} disp_k μ t`.  In the chart, `core` has normalized
  coordinates `(u² + μ ε u χ, u³)` (`chart_core`) — ce:rounding-formula.
* **Time.** `SpatialFamily` indexes the slices by all of `ℝ` and demands embedded slices everywhere; the
  printed formula is only claimed embedded on `[0, 1]` ("embeddedness outside [0,1] is not claimed").  The
  family is therefore `G λ = slice (φ λ)` with `φ = Real.smoothTransition` (`φ 0 = 0`, `φ 1 = 1`, `φ λ ∈ (0,1]`
  for `λ > 0`): on `[0,1]` it is the printed family in the reparametrized time `μ = φ(λ)`. -/

namespace SpatialLink

variable {c : ℕ} (L : SpatialLink c)

/-! ### 4.1 Unit P′ — the periodic cutoff from the accepted transition profile -/

/-- the 1-periodic smooth cutoff of radius `r` (for `0 < r < 1/2`): `1` where `dist(s, ℤ) ≤ r/2`, `0`
where `dist(s, ℤ) ≥ r`, values in `[0, 1]` — the printed `ρ` in the parameter -/
def periodicBump (r s : ℝ) : ℝ :=
  Real.smoothTransition ((Real.cos (2 * Real.pi * s) - Real.cos (2 * Real.pi * r)) /
    (Real.cos (Real.pi * r) - Real.cos (2 * Real.pi * r)))

theorem periodicBump_contDiff (r : ℝ) : ContDiff ℝ ∞ (periodicBump r) := by
  unfold periodicBump
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem periodicBump_periodic (r : ℝ) : Function.Periodic (periodicBump r) 1 := by
  intro s
  simp only [periodicBump, mul_add, mul_one]
  rw [Real.cos_add_two_pi]

theorem periodicBump_nonneg (r s : ℝ) : 0 ≤ periodicBump r s := Real.smoothTransition.nonneg _

theorem periodicBump_le_one (r s : ℝ) : periodicBump r s ≤ 1 := Real.smoothTransition.le_one _

/-- `ρ(0) = 1` ("equal to one near zero"; `cos 0 = 1 ≥ cos πr`) -/
theorem periodicBump_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) : periodicBump r 0 = 1 := by
  sorry

/-- `ρ = 1` on `dist(s, ℤ) ≤ r/2` -/
theorem periodicBump_eq_one {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ} {n : ℤ}
    (hs : |s - n| ≤ r / 2) : periodicBump r s = 1 := by
  sorry

/-- "with support strictly inside": `ρ = 0` where `dist(s, ℤ) ≥ r` -/
theorem periodicBump_eq_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ}
    (hs : ∀ n : ℤ, r ≤ |s - n|) : periodicBump r s = 0 := by
  sorry

theorem exists_int_abs_lt_of_periodicBump_ne_zero {r : ℝ} (hr : 0 < r) (hr' : r < 1 / 2) {s : ℝ}
    (hs : periodicBump r s ≠ 0) : ∃ n : ℤ, |s - n| < r := by
  by_contra h
  push Not at h
  exact hs (periodicBump_eq_zero hr hr' h)

/-! ### 4.2 The exact germ data and the positive chart (sm-3:3060-3072) -/

/-- the data of one exact cusp germ (ce:exact-germ), with the chart interval shrunk to `δ ≤ 1/3` so
that it embeds in the circle -/
structure GermData (i : Fin c) (t₀ : ℝ) where
  A : ℝ
  δ : ℝ
  A_ne : A ≠ 0
  δ_pos : 0 < δ
  δ_le : δ ≤ 1 / 3
  /-- "on a parameter interval with smooth coordinate u = y − y₀" -/
  y_deriv_ne : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), deriv (yOf (L.T i)) t ≠ 0
  /-- the three displayed formulas -/
  formula : ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
    L.T i t = ((L.T i t₀).1 + A * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2,
      yOf (L.T i) t,
      (L.T i t₀).2.2 + A * yOf (L.T i) t₀ * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2
        + (2 * A / 3) * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 3)

/-- the printed hypothesis supplies the data (shrink `δ` to `min δ (1/3)`) -/
theorem exists_germData {i : Fin c} {t₀ : ℝ} (h : L.ExactCuspGerm i t₀) :
    Nonempty (L.GermData i t₀) := by
  sorry

namespace GermData

variable {L} {i : Fin c} {t₀ : ℝ}

/-- `x₀` (the germ data only fixes the cusp; the argument is for field notation) -/
def x₀ (_g : L.GermData i t₀) : ℝ := (L.T i t₀).1
/-- `y₀` -/
def y₀ (_g : L.GermData i t₀) : ℝ := yOf (L.T i) t₀
/-- `z₀` -/
def z₀ (_g : L.GermData i t₀) : ℝ := (L.T i t₀).2.2

variable (g : L.GermData i t₀)
/-- the chart coordinate `u = y − y₀`, as a function of the parameter -/
def u (t : ℝ) : ℝ := yOf (L.T i) t - g.y₀
/-- the chart interval -/
def J : Set ℝ := Set.Ioo (t₀ - g.δ) (t₀ + g.δ)
/-- ce:positive-chart: `X = (x − x₀)/A`, `Z = 3(z − z₀ − y₀(x − x₀))/(2A)` -/
def chart (p : Plane) : Plane :=
  ((p.1 - g.x₀) / g.A, 3 * (p.2 - g.z₀ - g.y₀ * (p.1 - g.x₀)) / (2 * g.A))
/-- its affine inverse -/
def unchart (w : Plane) : Plane :=
  (g.x₀ + g.A * w.1, g.z₀ + g.y₀ * g.A * w.1 + (2 * g.A / 3) * w.2)

theorem u_t₀ : g.u t₀ = 0 := by simp [u, y₀]

theorem u_smooth : ContDiff ℝ ∞ g.u := ((L.smooth i).snd.fst).sub contDiff_const

theorem t₀_mem_J : t₀ ∈ g.J := ⟨by linarith [g.δ_pos], by linarith [g.δ_pos]⟩

theorem isOpen_J : IsOpen g.J := isOpen_Ioo

theorem chart_unchart (w : Plane) : g.chart (g.unchart w) = w := by
  have hA := g.A_ne
  ext <;> simp only [chart, unchart] <;> field_simp <;> ring

theorem unchart_chart (p : Plane) : g.unchart (g.chart p) = p := by
  have hA := g.A_ne
  ext <;> simp only [chart, unchart] <;> field_simp <;> ring

theorem chart_injective : Function.Injective g.chart :=
  Function.LeftInverse.injective g.unchart_chart

theorem unchart_continuous : Continuous g.unchart := by
  unfold unchart; fun_prop

theorem chart_continuous : Continuous g.chart := by
  unfold chart; fun_prop

/-- "sends the front to `(u², u³)`" -/
theorem chart_proj {t : ℝ} (ht : t ∈ g.J) : g.chart (xzOf (L.T i) t) = (g.u t ^ 2, g.u t ^ 3) := by
  sorry

/-- the chart is affine: the displacement `(s, 0, y₀ s)` (physical, ce:physical-displacement) is the
normalized displacement `(s, 0)` -/
theorem chart_add_disp (p : Plane) (s : ℝ) :
    g.chart (p + s • ((g.A : ℝ), g.A * g.y₀)) = g.chart p + (s, 0) := by
  have hA := g.A_ne
  ext <;> simp only [chart, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, Prod.fst_zero,
    Prod.snd_zero] <;> field_simp <;> ring

/-- `u` is strictly monotone or strictly antitone on the chart interval (`u' = y' ≠ 0` there,
continuous, so of one sign: "The coordinate u may increase or decrease") -/
theorem u_strictMonoOn_or_strictAntiOn : StrictMonoOn g.u g.J ∨ StrictAntiOn g.u g.J := by
  sorry

theorem u_injOn : Set.InjOn g.u g.J := by
  rcases g.u_strictMonoOn_or_strictAntiOn with h | h
  · exact h.injOn
  · exact h.injOn

/-- "The cubic coordinate is injective" (ce:cubic-difference) -/
theorem cube_injective : Function.Injective (fun u : ℝ => u ^ 3) :=
  (Odd.strictMono_pow (by decide : Odd 3)).injective

/-- "hence the full local arc is injective even at its cusp" -/
theorem proj_injOn_J : Set.InjOn (xzOf (L.T i)) g.J := by
  intro s hs t ht he
  have h1 := g.chart_proj hs
  have h2 := g.chart_proj ht
  rw [he, h2] at h1
  have h3 : g.u t ^ 3 = g.u s ^ 3 := (Prod.ext_iff.mp h1).2
  exact g.u_injOn hs ht (cube_injective h3).symm

/-! #### The rectangle package of a cusp interval `[t₀ − η, t₀ + η]` -/

/-- the smaller end value of `u` -/
def uMin (η : ℝ) : ℝ := min (g.u (t₀ - η)) (g.u (t₀ + η))
/-- the larger end value of `u` -/
def uMax (η : ℝ) : ℝ := max (g.u (t₀ - η)) (g.u (t₀ + η))
/-- `M = max(|u₋|, |u₊|)`, the bound of `|u|` on the interval -/
def M (η : ℝ) : ℝ := max |g.uMin η| |g.uMax η|
/-- the clean rectangle in normalized coordinates -/
def rect (η : ℝ) : Set Plane :=
  Set.Icc (-(g.M η) ^ 2) (2 * (g.M η) ^ 2) ×ˢ Set.Icc ((g.uMin η) ^ 3) ((g.uMax η) ^ 3)
/-- the sup-norm radius of the rectangle -/
def radius (η : ℝ) : ℝ := max (2 * (g.M η) ^ 2) ((g.M η) ^ 3)

theorem rect_convex (η : ℝ) : Convex ℝ (g.rect η) := (convex_Icc _ _).prod (convex_Icc _ _)

theorem rect_isCompact (η : ℝ) : IsCompact (g.rect η) := isCompact_Icc.prod isCompact_Icc

theorem rect_subset_closedBall (η : ℝ) : g.rect η ⊆ Metric.closedBall 0 (g.radius η) := by
  sorry

/-- for `0 < η < δ` the two end values of `u` have opposite signs: `u₋ < 0 < u₊` -/
theorem uMin_neg {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : g.uMin η < 0 := by
  sorry

theorem uMax_pos {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : 0 < g.uMax η := by
  sorry

theorem M_pos {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) : 0 < g.M η :=
  lt_of_lt_of_le (abs_pos.mpr (g.uMax_pos hη hηδ).ne') (le_max_right _ _)

/-- on the closed cusp interval `u` runs through `[u₋, u₊]` -/
theorem u_mem_Icc_of_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₀ - η) (t₀ + η)) : g.u t ∈ Set.Icc (g.uMin η) (g.uMax η) := by
  sorry

/-- and, conversely, a chart parameter whose `u` lies in `[u₋, u₊]` is on the closed interval -/
theorem mem_Icc_of_u_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ} (ht : t ∈ g.J)
    (hu : g.u t ∈ Set.Icc (g.uMin η) (g.uMax η)) : t ∈ Set.Icc (t₀ - η) (t₀ + η) := by
  sorry

/-- on the open interval `u` is strictly inside `(u₋, u₊)` -/
theorem u_mem_Ioo_of_mem {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Ioo (t₀ - η) (t₀ + η)) : g.u t ∈ Set.Ioo (g.uMin η) (g.uMax η) := by
  sorry

theorem abs_u_le_M {η : ℝ} (hη : 0 < η) (hηδ : η < g.δ) {t : ℝ}
    (ht : t ∈ Set.Icc (t₀ - η) (t₀ + η)) : |g.u t| ≤ g.M η := by
  sorry

end GermData

/-! ### 4.3 The choices at one cusp (sm-3:3073-3096, "Disjoint clean supports and positive charts") -/

/-- The constants chosen at the cusp `k`: the germ data, the half-width `η` of the cusp parameter
interval `[t₀ − η, t₀ + η]` inside the chart, the cutoff radius `r < η`, the amplitude `ε ≤ M`, and the
clearance `remote`: every parameter of another circle, or of this circle outside the chart interval
(modulo the period), projects outside the normalized square of radius `radius η` — the printed "a
sufficiently small open page neighbourhood V meets only the exact-chart arc". -/
structure CuspChoice (k : L.cuspSet) where
  g : L.GermData k.1.1 k.1.2
  η : ℝ
  r : ℝ
  ε : ℝ
  η_pos : 0 < η
  η_lt : η < g.δ
  r_pos : 0 < r
  r_lt : r < η
  ε_pos : 0 < ε
  ε_le : ε ≤ g.M η
  remote : ∀ q : Param c, (q.1 ≠ k.1.1 ∨ ∀ n : ℤ, q.2 + n ∉ g.J) →
    g.radius η < ‖g.chart (xzOf (L.T q.1) q.2)‖

namespace CuspChoice

variable {L} {k : L.cuspSet} (ch : L.CuspChoice k)

/-- the left end of the cusp parameter interval -/
def a : ℝ := k.1.2 - ch.η
/-- the right end -/
def b : ℝ := k.1.2 + ch.η
/-- the clean neighbourhood: the rectangle pulled back by the inverse chart -/
def U : Set Plane := ch.g.unchart '' ch.g.rect ch.η
/-- the cutoff in the parameter -/
def chi (t : ℝ) : ℝ := periodicBump ch.r (t - k.1.2)
/-- ce:physical-displacement at time `μ`: `Δx = A μ ε u ρ`, `Δy = 0`, `Δz = A y₀ μ ε u ρ` -/
def disp (μ t : ℝ) : Space :=
  (μ * ch.ε * ch.g.A * ch.g.u t * ch.chi t) • ((1 : ℝ), (0 : ℝ), ch.g.y₀)

theorem a_lt : ch.a < k.1.2 := by unfold a; linarith [ch.η_pos]
theorem lt_b : k.1.2 < ch.b := by unfold b; linarith [ch.η_pos]
theorem len : ch.b - ch.a < 1 := by
  unfold a b; linarith [ch.η_lt, ch.g.δ_le]
theorem r_lt_half : ch.r < 1 / 2 := by linarith [ch.r_lt, ch.η_lt, ch.g.δ_le]

theorem Icc_subset_J : Set.Icc ch.a ch.b ⊆ ch.g.J := fun t ht =>
  ⟨by unfold a at ht; linarith [ht.1, ch.η_lt], by unfold b at ht; linarith [ht.2, ch.η_lt]⟩

theorem chi_contDiff : ContDiff ℝ ∞ ch.chi :=
  (periodicBump_contDiff ch.r).comp (contDiff_id.sub contDiff_const)

theorem chi_periodic : Function.Periodic ch.chi 1 := fun t => by
  simp only [chi]
  rw [show t + 1 - k.1.2 = (t - k.1.2) + 1 by ring]
  exact periodicBump_periodic ch.r _

theorem chi_nonneg (t : ℝ) : 0 ≤ ch.chi t := periodicBump_nonneg _ _
theorem chi_le_one (t : ℝ) : ch.chi t ≤ 1 := periodicBump_le_one _ _

theorem chi_cusp : ch.chi k.1.2 = 1 := by
  simp only [chi, sub_self]
  exact periodicBump_zero ch.r_pos ch.r_lt_half

/-- the cutoff vanishes off the open cusp interval (modulo the period): "The cutoff vanishes on
collars of the chart ends" -/
theorem chi_eq_zero_of_notMem {t : ℝ} (h : ∀ n : ℤ, t + n ∉ Set.Ioo ch.a ch.b) : ch.chi t = 0 := by
  sorry

theorem disp_zero (t : ℝ) : ch.disp 0 t = 0 := by simp [disp]

theorem disp_eq_zero_of_notMem (μ : ℝ) {t : ℝ} (h : ∀ n : ℤ, t + n ∉ Set.Ioo ch.a ch.b) :
    ch.disp μ t = 0 := by
  simp [disp, ch.chi_eq_zero_of_notMem h]

/-- `Δy = 0` -/
theorem disp_snd_fst (μ t : ℝ) : (ch.disp μ t).2.1 = 0 := by simp [disp]

theorem disp_contDiff (μ : ℝ) : ContDiff ℝ ∞ (ch.disp μ) := by
  unfold disp
  have h1 := ch.g.u_smooth
  have h2 := ch.chi_contDiff
  fun_prop

theorem disp_periodic (μ : ℝ) : Function.Periodic (ch.disp μ) 1 := fun t => by
  simp only [disp, GermData.u, chi]
  rw [show t + 1 - k.1.2 = (t - k.1.2) + 1 by ring, periodicBump_periodic]
  have : yOf (L.T k.1.1) (t + 1) = yOf (L.T k.1.1) t := by
    simp only [yOf, L.periodic k.1.1 t]
  rw [this]

/-- the projected displacement is `(μ ε u χ) • (A, A y₀)` -/
theorem xz_disp (μ t : ℝ) :
    ((ch.disp μ t).1, (ch.disp μ t).2.2) =
      (μ * ch.ε * ch.g.u t * ch.chi t) • ((ch.g.A : ℝ), ch.g.A * ch.g.y₀) := by
  simp only [disp, Prod.smul_mk, smul_eq_mul]
  ext <;> simp <;> ring

theorem isDisc_U : IsDisc ch.U := by
  sorry

theorem center_mem_interior_U : xzOf (L.T k.1.1) k.1.2 ∈ interior ch.U := by
  sorry

/-- points of `U` have normalized sup-norm at most `radius` -/
theorem norm_chart_le_of_mem_U {p : Plane} (hp : p ∈ ch.U) :
    ‖ch.g.chart p‖ ≤ ch.g.radius ch.η := by
  obtain ⟨w, hw, rfl⟩ := hp
  rw [ch.g.chart_unchart]
  simpa using ch.g.rect_subset_closedBall ch.η hw

/-- `p ∈ U` iff its chart lies in the rectangle -/
theorem mem_U_iff (p : Plane) : p ∈ ch.U ↔ ch.g.chart p ∈ ch.g.rect ch.η := by
  constructor
  · rintro ⟨w, hw, rfl⟩; rw [ch.g.chart_unchart]; exact hw
  · intro h; exact ⟨_, h, ch.g.unchart_chart p⟩

/-- "clean": the arc lies in `U` (sm-3:3080-3082) -/
theorem arc_in {t : ℝ} (ht : t ∈ Set.Icc ch.a ch.b) : xzOf (L.T k.1.1) t ∈ ch.U := by
  sorry

/-- "clean": a point of the projection in `U` lies on the closed cusp arc (modulo the period) — the
remote parameters are excluded by `remote`, the chart parameters by the monotonicity of `Z = u³` -/
theorem clean {q : Param c} (hq : xzOf (L.T q.1) q.2 ∈ ch.U) :
    q.1 = k.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ Set.Icc ch.a ch.b := by
  sorry

/-- the closed arc carries no double point of `L` -/
theorem arc_simple {t : ℝ} (ht : t ∈ Set.Icc ch.a ch.b) {q : Param c}
    (hq : ¬ SameParam (k.1.1, t) q) : xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t := by
  sorry

end CuspChoice

/-! ### 4.4 The global choices and the rounding family (sm-3:3097-3119) -/

/-- The complete package of choices: one `CuspChoice` at every cusp, with pairwise disjoint clean
neighbourhoods ("shrink their neighbourhoods to make them pairwise disjoint"). -/
structure Choices where
  fin : Fintype L.cuspSet
  ch : ∀ k : L.cuspSet, L.CuspChoice k
  disjoint : ∀ k k', k ≠ k' → Disjoint (ch k).U (ch k').U

namespace Choices

variable {L} (C : L.Choices)

/-- the rounded link at time `μ`: `L` plus the displacements of the cusps of each circle -/
def core (μ : ℝ) (i : Fin c) (t : ℝ) : Space :=
  letI : Fintype L.cuspSet := C.fin
  L.T i t + ∑ k : L.cuspSet, if k.1.1 = i then (C.ch k).disp μ t else 0

theorem core_zero : C.core 0 = L.T := by
  funext i t
  simp [core, CuspChoice.disp_zero]

theorem core_contDiff (μ : ℝ) (i : Fin c) : ContDiff ℝ ∞ (C.core μ i) := by
  letI : Fintype L.cuspSet := C.fin
  unfold core
  apply (L.smooth i).add
  apply ContDiff.sum
  intro k _
  split_ifs
  · exact (C.ch k).disp_contDiff μ
  · exact contDiff_const

theorem core_periodic (μ : ℝ) (i : Fin c) : Function.Periodic (C.core μ i) 1 := by
  letI : Fintype L.cuspSet := C.fin
  intro t
  unfold core
  rw [L.periodic i t]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · exact (C.ch k).disp_periodic μ t
  · rfl

/-- joint smoothness in `(λ, t)` of the time-clamped family -/
theorem core_joint_contDiff (i : Fin c) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => C.core (Real.smoothTransition p.1) i p.2) := by
  sorry

/-- `Δy = 0`: the height function is untouched -/
theorem yOf_core (μ : ℝ) (i : Fin c) : yOf (C.core μ i) = yOf (L.T i) := by
  letI : Fintype L.cuspSet := C.fin
  funext t
  simp only [yOf, core, Prod.snd_add, Prod.fst_add]
  have : (∑ k : L.cuspSet, if k.1.1 = i then (C.ch k).disp μ t else 0).2.1 = 0 := by
    rw [Prod.snd_sum, Prod.fst_sum]
    apply Finset.sum_eq_zero
    intro k _
    split_ifs
    · exact (C.ch k).disp_snd_fst μ t
    · rfl
  rw [this, add_zero]

/-- "fixed outside disjoint cusp parameter intervals" -/
theorem core_eq_of_notMem (μ : ℝ) (i : Fin c) {t : ℝ}
    (h : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (C.ch k).a (C.ch k).b) :
    C.core μ i t = L.T i t := by
  letI : Fintype L.cuspSet := C.fin
  unfold core
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro k _
  split_ifs with hk
  · exact (C.ch k).disp_eq_zero_of_notMem μ (h k hk)
  · rfl

/-- the projection of the rounded link at time `μ`, as plain loops (no embeddedness needed) -/
def coreLoop (μ : ℝ) (i : Fin c) : SmoothLoop where
  γ := xzOf (C.core μ i)
  smooth := ((C.core_contDiff μ i).fst).prodMk ((C.core_contDiff μ i).snd.snd)
  periodic := fun t => by
    show xzOf (C.core μ i) (t + 1) = xzOf (C.core μ i) t
    simp only [xzOf, xOf, zOf, C.core_periodic μ i t]

@[simp] theorem coreLoop_γ (μ : ℝ) (i : Fin c) : (C.coreLoop μ i).γ = xzOf (C.core μ i) := rfl

/-! ### 4.5 The local analysis on one cusp arc (sm-3:3099-3131) -/

/-- on the open arc of `k` the other cusps of the circle contribute nothing (their cutoffs vanish:
the arcs are disjoint on the circle since the discs are and `arc_in`) -/
theorem chi_eq_zero_of_ne {k k' : L.cuspSet} (hne : k ≠ k') (hi : k.1.1 = k'.1.1) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) : (C.ch k').chi t = 0 := by
  sorry

/-- on the open arc of `k` the rounded link is `L` plus the displacement of `k` alone -/
theorem core_on_arc (μ : ℝ) (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) :
    C.core μ k.1.1 t = L.T k.1.1 t + (C.ch k).disp μ t := by
  sorry

/-- ce:rounding-formula: in the normalized chart the rounded arc is `(u² + μ ε u ρ, u³)` -/
theorem chart_core (μ : ℝ) (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) :
    (C.ch k).g.chart (xzOf (C.core μ k.1.1) t) =
      ((C.ch k).g.u t ^ 2 + μ * (C.ch k).ε * (C.ch k).g.u t * (C.ch k).chi t, (C.ch k).g.u t ^ 3) := by
  sorry

/-- "keep every moved point inside V": the rounded arc stays in `U` for `0 ≤ μ ≤ 1` -/
theorem inside {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) : xzOf (C.core μ k.1.1) t ∈ (C.ch k).U := by
  sorry

/-- "the two projected derivatives are never simultaneously zero for λ > 0": `dZ/du = 3u² ≠ 0` off
the centre, `dX/du = μ ε ρ(0) = μ ε` at the centre; composed with the smooth coordinate `u` (either
direction) -/
theorem arc_regular {μ : ℝ} (hμ : 0 < μ) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) : deriv (xzOf (C.core μ k.1.1)) t ≠ 0 := by
  sorry

/-- "distinct parameters anywhere in that chart have different projected points at every λ"
(ce:cubic-difference: `Z = u³` is injective) -/
theorem arc_injOn (μ : ℝ) (k : L.cuspSet) :
    Set.InjOn (xzOf (C.core μ k.1.1)) (Set.Ioo (C.ch k).a (C.ch k).b) := by
  sorry

/-- "a moved point cannot meet a remote parameter … different modifications cannot meet each other
… together with strict local injectivity these facts exclude every new projected crossing" -/
theorem arc_no_crossing {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (C.ch k).a (C.ch k).b) {q : Param c} (hq : ¬ SameParam (k.1.1, t) q) :
    xzOf (C.core μ q.1) q.2 ≠ xzOf (C.core μ k.1.1) t := by
  sorry

/-- the clean cusp smoothing witness at every time `0 < μ ≤ 1` -/
def smoothing {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) : L.CleanCuspSmoothing (C.coreLoop μ) where
  U := fun k => (C.ch k).U
  a := fun k => (C.ch k).a
  b := fun k => (C.ch k).b
  disc := fun k => (C.ch k).isDisc_U
  center := fun k => (C.ch k).center_mem_interior_U
  disjoint := C.disjoint
  a_lt := fun k => (C.ch k).a_lt
  lt_b := fun k => (C.ch k).lt_b
  len := fun k => (C.ch k).len
  clean := fun k q hq => (C.ch k).clean hq
  arc_in := fun k t ht => (C.ch k).arc_in ht
  arc_simple := fun k t ht q hq => (C.ch k).arc_simple ht hq
  agree := fun i t h => by
    show xzOf (C.core μ i) t = xzOf (L.T i) t
    rw [xzOf, xzOf, xOf, zOf, xOf, zOf, C.core_eq_of_notMem μ i h]
  inside := fun k t ht => C.inside ⟨hμ.le, hμ1⟩ k ht
  regular := fun k t ht => C.arc_regular hμ k ht
  simple := fun k => C.arc_injOn μ k
  no_crossing := fun k t ht q hq => C.arc_no_crossing ⟨hμ.le, hμ1⟩ k ht hq

end Choices

/-! ### 4.6 Consequences of a clean cusp smoothing (transcription of the accepted
`GeomRounding` consequences, SM/FrontSmooth.lean 1170-1456 and SM/FrontRecordBridge.lean §3, to the
plain loop families of `CleanCuspSmoothing`; shared with the row-90 unit) -/

namespace CleanCuspSmoothing

variable {L} {G : Fin c → SmoothLoop} (ρ : L.CleanCuspSmoothing G)
include ρ

/-- "creates no crossing": the double points of the smoothing, as pairs of parameters of the shared
circles, are exactly those of `L`'s projection (`GeomRounding.isDouble_iff`) -/
theorem isDoubleOf_iff (p q : Param c) : IsDoubleOf G p q ↔ IsDoubleOf L.projLoop p q := by
  sorry

/-- at a double point of `L` the germ, hence the velocity, of the smoothing is `L`'s
(`GeomRounding.deriv_eq_of_isDouble`) -/
theorem deriv_eq_of_isDouble {p q : Param c} (h : IsDoubleOf L.projLoop p q) :
    deriv (G p.1).γ p.2 = deriv (xzOf (L.T p.1)) p.2 := by
  sorry

/-- the smoothing is regular everywhere: on the arcs by `regular`, elsewhere its velocity is `L`'s,
nonzero since every cusp lies strictly inside its own arc (`GeomRounding.regular_everywhere`) -/
theorem regular_everywhere (hfin : L.cuspSet.Finite) (i : Fin c) (t : ℝ) : deriv (G i).γ t ≠ 0 := by
  sorry

/-- the crossing occurrences are the same parameters (`GeomRounding.occSetOf_eq`) -/
theorem occSetOf_eq : occSetOf G = occSetOf L.projLoop := by
  sorry

/-- the cusp arcs of one circle are disjoint on the circle (their discs are disjoint and each arc
lies in its disc) -/
theorem intervals_disjoint (k k' : L.cuspSet) (hne : k ≠ k') (hi : k.1.1 = k'.1.1) (n : ℤ) :
    Disjoint (Set.Ioo (ρ.a k) (ρ.b k)) (Set.Ioo (ρ.a k' + n) (ρ.b k' + n)) := by
  sorry

theorem crossSignOf_eq {p q : Param c} (h : IsDoubleOf L.projLoop p q) :
    crossSignOf G p q = crossSignOf L.projLoop p q := by
  unfold crossSignOf
  rw [ρ.deriv_eq_of_isDouble h, ρ.deriv_eq_of_isDouble h.symm]
  rfl

end CleanCuspSmoothing

/-! ### 4.7 The slices are spatial embeddings (sm-3:3145-3153) and the family -/

namespace Choices

variable {L} (C : L.Choices)

/-- two `SmoothLoop`s with the same map are equal -/
theorem _root_.SM.SmoothLoop.ext' {a b : SmoothLoop} (h : a.γ = b.γ) : a = b := by
  cases a; cases b; cases h; rfl

theorem coreLoop_zero : C.coreLoop 0 = L.projLoop := by
  funext i
  apply SmoothLoop.ext'
  show xzOf (C.core 0 i) = xzOf (L.T i)
  rw [C.core_zero]

/-- "Spatial injectivity follows for the whole family": a spatial coincidence would project to a new
coincidence (excluded) or to an old double point (distinct unchanged heights) -/
theorem core_embedded (h : L.CuspedProjection) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin c) (s t : ℝ) (he : C.core μ i s = C.core μ j t) : i = j ∧ SameT s t := by
  by_contra hne
  have hns : ¬ SameParam (i, s) (j, t) := fun ⟨h1, n, hn⟩ => hne ⟨h1, n, hn⟩
  have hxz : xzOf (C.core μ i) s = xzOf (C.core μ j) t := by
    simp only [xzOf, xOf, zOf, he]
  have hy : yOf (C.core μ i) s = yOf (C.core μ j) t := by simp only [yOf, he]
  rw [C.yOf_core, C.yOf_core] at hy
  have hd : IsDoubleOf L.projLoop (i, s) (j, t) := by
    rcases eq_or_lt_of_le hμ.1 with h0 | h0
    · subst h0
      refine ⟨hns, ?_⟩
      show xzOf (L.T i) s = xzOf (L.T j) t
      rwa [C.core_zero] at hxz
    · exact ((C.smoothing h0 hμ.2).isDoubleOf_iff (i, s) (j, t)).mp ⟨hns, hxz⟩
  exact h.heights_distinct _ _ hd hy

/-- the derivative of a smooth spatial map is the triple of the derivatives of its coordinates (the
pattern of the accepted `TransverseKnot.deriv_T`) -/
theorem _root_.SM.deriv_space {T : ℝ → Space} (hT : ContDiff ℝ ∞ T) (t : ℝ) :
    deriv T t = (deriv (xOf T) t, deriv (yOf T) t, deriv (zOf T) t) := by
  have hx : HasDerivAt (xOf T) (deriv (xOf T) t) t :=
    ((hT.fst).differentiable (by simp) t).hasDerivAt
  have hy : HasDerivAt (yOf T) (deriv (yOf T) t) t :=
    ((hT.snd.fst).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivAt (zOf T) (deriv (zOf T) t) t :=
    ((hT.snd.snd).differentiable (by simp) t).hasDerivAt
  exact (hx.prodMk (hy.prodMk hz)).deriv

/-- and the derivative of its `xz` projection is the pair (`TransverseKnot.deriv_xz`) -/
theorem _root_.SM.deriv_xzOf {T : ℝ → Space} (hT : ContDiff ℝ ∞ T) (t : ℝ) :
    deriv (xzOf T) t = (deriv (xOf T) t, deriv (zOf T) t) := by
  have hx : HasDerivAt (xOf T) (deriv (xOf T) t) t :=
    ((hT.fst).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivAt (zOf T) (deriv (zOf T) t) t :=
    ((hT.snd.snd).differentiable (by simp) t).hasDerivAt
  exact (hx.prodMk hz).deriv

/-- "Spatial immersion holds for every λ because `dy/du = 1` in each modified chart and the rest of
`L` is unchanged" — here: the projected velocity is nonzero for `μ > 0` (`regular_everywhere`), and at
`μ = 0` the link is `L` -/
theorem core_regular (h : L.CuspedProjection) {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (i : Fin c)
    (t : ℝ) : deriv (C.core μ i) t ≠ 0 := by
  rcases eq_or_lt_of_le hμ.1 with h0 | h0
  · subst h0; rw [C.core_zero]; exact L.regular i t
  · intro h0'
    have hreg := (C.smoothing h0 hμ.2).regular_everywhere h.cusps_finite i t
    apply hreg
    show deriv (xzOf (C.core μ i)) t = 0
    rw [deriv_space (C.core_contDiff μ i)] at h0'
    rw [deriv_xzOf (C.core_contDiff μ i)]
    have h1 := (Prod.ext_iff.mp h0').1
    have h2 := (Prod.ext_iff.mp (Prod.ext_iff.mp h0').2).2
    simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
    rw [h1, h2]
    rfl

/-- the slice at time `μ ∈ [0, 1]` as a `SpatialLink` -/
def slice (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : SpatialLink c where
  T := C.core μ
  smooth := C.core_contDiff μ
  periodic := C.core_periodic μ
  embedded := C.core_embedded h ⟨h0, h1⟩
  regular := C.core_regular h ⟨h0, h1⟩

@[simp] theorem slice_T (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (C.slice h h0 h1).T = C.core μ := rfl

theorem slice_projLoop (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    (C.slice h h0 h1).projLoop = C.coreLoop μ := by
  funext i
  apply SmoothLoop.ext'
  rfl

theorem slice_height (h : L.CuspedProjection) {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (p : Param c) :
    (C.slice h h0 h1).height p = L.height p := by
  show yOf (C.core μ p.1) p.2 = yOf (L.T p.1) p.2
  rw [C.yOf_core]

/-- the printed family in the clamped time `μ = φ(λ)`, `φ = Real.smoothTransition` -/
def fam (h : L.CuspedProjection) : SpatialFamily c where
  G := fun lam => C.slice h (Real.smoothTransition.nonneg lam) (Real.smoothTransition.le_one lam)
  joint_smooth := C.core_joint_contDiff

theorem fam_G (h : L.CuspedProjection) (lam : ℝ) :
    (C.fam h).G lam = C.slice h (Real.smoothTransition.nonneg lam) (Real.smoothTransition.le_one lam) :=
  rfl

theorem fam_zero (h : L.CuspedProjection) : (C.fam h).G 0 = L := by
  apply ext'
  rw [fam_G, slice_T, Real.smoothTransition.zero, C.core_zero]

/-- for `λ > 0` the slice of the family is a positive slice `μ ∈ (0, 1]` -/
theorem smoothTransition_mem {lam : ℝ} (hlam : 0 < lam) :
    0 < Real.smoothTransition lam ∧ Real.smoothTransition lam ≤ 1 :=
  ⟨Real.smoothTransition.pos_of_pos hlam, Real.smoothTransition.le_one lam⟩

/-- every positive slice is an ordinary finite regular generic diagram -/
theorem slice_generic (h : L.CuspedProjection) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (C.slice h hμ.le hμ1).RegularGenericProjection := by
  have ρ := C.smoothing hμ hμ1
  have hpl := C.slice_projLoop h hμ.le hμ1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i t
    exact ρ.regular_everywhere h.cusps_finite i t
  · rw [hpl, ρ.occSetOf_eq]; exact h.doubles_finite
  · intro p q hd
    rw [hpl] at hd
    have hd' := (ρ.isDoubleOf_iff p q).mp hd
    have h1 := ρ.deriv_eq_of_isDouble hd'
    have h2 := ρ.deriv_eq_of_isDouble hd'.symm
    simp only [coreLoop_γ] at h1 h2
    rw [slice_T, h1, h2]
    exact h.transverse p q hd'
  · intro p q r hpq hqr hpr
    rw [hpl] at hpq hqr hpr
    exact h.no_triple p q r ((ρ.isDoubleOf_iff p q).mp hpq) ((ρ.isDoubleOf_iff q r).mp hqr)
      ((ρ.isDoubleOf_iff p r).mp hpr)
  · intro p q hd
    rw [hpl] at hd
    rw [C.slice_height, C.slice_height]
    exact h.heights_distinct p q ((ρ.isDoubleOf_iff p q).mp hd)

/-! ### 4.8 Existence of the choices (sm-3:3073-3096) -/

end Choices

/-- distinct cusps have distinct images (a common image would be a double point at a cusp,
excluded by `transverse`) -/
theorem cusp_image_injective (h : L.CuspedProjection) (k k' : L.cuspSet)
    (he : xzOf (L.T k.1.1) k.1.2 = xzOf (L.T k'.1.1) k'.1.2) : k = k' := by
  sorry

/-- finitely many distinct cusp images have a positive minimal gap -/
theorem exists_gap (h : L.CuspedProjection) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ k k' : L.cuspSet, k ≠ k' →
      2 * gap < dist (xzOf (L.T k.1.1) k.1.2) (xzOf (L.T k'.1.1) k'.1.2) := by
  sorry

/-- "Its distance from that complement is positive": the cusp image is not in the compact projected
image of the complement of the chart interval (nor of the other circles), so its normalized distance
is positive -/
theorem exists_remote_clearance (h : L.CuspedProjection) (k : L.cuspSet)
    (g : L.GermData k.1.1 k.1.2) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : Param c, (q.1 ≠ k.1.1 ∨ ∀ n : ℤ, q.2 + n ∉ g.J) →
      d < ‖g.chart (xzOf (L.T q.1) q.2)‖ := by
  sorry

/-- "Choose b > 0 so small that the closed subarc lies inside V": by continuity of `u` at `t₀` the
rectangle radius tends to `0` with `η`, and the physical neighbourhood `U` shrinks to the cusp
image -/
theorem exists_eta (k : L.cuspSet) (g : L.GermData k.1.1 k.1.2) {d ρ₀ : ℝ} (hd : 0 < d)
    (hρ₀ : 0 < ρ₀) :
    ∃ η : ℝ, 0 < η ∧ η < g.δ ∧ g.radius η < d ∧
      g.unchart '' g.rect η ⊆ Metric.closedBall (xzOf (L.T k.1.1) k.1.2) ρ₀ := by
  sorry

/-- the choices at one cusp, with the clean neighbourhood inside a prescribed ball about the cusp
image -/
theorem exists_cuspChoice_within (h : L.CuspedProjection) (k : L.cuspSet) {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) :
    ∃ ch : L.CuspChoice k, ch.U ⊆ Metric.closedBall (xzOf (L.T k.1.1) k.1.2) ρ₀ := by
  obtain ⟨g⟩ := L.exists_germData (h.exact_germ k.1 k.2)
  obtain ⟨d, hd, hremote⟩ := L.exists_remote_clearance h k g
  obtain ⟨η, hη, hηδ, hrad, hsub⟩ := L.exists_eta k g hd hρ₀
  refine ⟨⟨g, η, η / 2, g.M η, hη, hηδ, by linarith, by linarith, g.M_pos hη hηδ, le_rfl,
    fun q hq => lt_trans hrad (hremote q hq)⟩, ?_⟩
  exact hsub

/-- "Make these choices at each of the finitely many cusps": the package of choices exists -/
theorem exists_choices (h : L.CuspedProjection) : Nonempty L.Choices := by
  obtain ⟨gap, hgap, hsep⟩ := L.exists_gap h
  have hch : ∀ k : L.cuspSet, ∃ ch : L.CuspChoice k,
      ch.U ⊆ Metric.closedBall (xzOf (L.T k.1.1) k.1.2) gap :=
    fun k => L.exists_cuspChoice_within h k hgap
  choose ch hch using hch
  refine ⟨{ fin := h.cusps_finite.fintype, ch := ch, disjoint := ?_ }⟩
  intro k k' hne
  apply Set.disjoint_of_subset (hch k) (hch k')
  exact Metric.closedBall_disjoint_closedBall (by linarith [hsep k k' hne])

/-! ## 5. Assembly: the witness `CuspRoundingFamily` from the choices (sm-3:3097-3170) -/

namespace Choices

variable {L} (C : L.Choices)

/-- the `CuspRoundingFamily` delivered by the construction -/
def witness (h : L.CuspedProjection) : CuspRoundingFamily L where
  fam := C.fam h
  start := C.fam_zero h
  a := fun k => (C.ch k).a
  b := fun k => (C.ch k).b
  a_lt := fun k => (C.ch k).a_lt
  lt_b := fun k => (C.ch k).lt_b
  len := fun k => (C.ch k).len
  intervals_disjoint := fun k k' hne hi n =>
    (C.smoothing (μ := 1) one_pos le_rfl).intervals_disjoint k k' hne hi n
  fixed_outside := fun lam i t ht => C.core_eq_of_notMem _ i ht
  generic := fun lam hlam h1 =>
    C.slice_generic h (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2
  clean := fun lam hlam h1 => by
    rw [fam_G, C.slice_projLoop]
    exact ⟨C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2⟩
  same_doubles := fun lam hlam h1 p q => by
    rw [fam_G, C.slice_projLoop]
    exact (C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2).isDoubleOf_iff p q
  same_velocity := fun lam hlam h1 p q hd =>
    (C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2).deriv_eq_of_isDouble hd
  same_data := fun lam hlam h1 p q hd => by
    refine ⟨?_, ?_⟩
    · rw [fam_G, C.slice_projLoop]
      exact (C.smoothing (smoothTransition_mem hlam).1 (smoothTransition_mem hlam).2).crossSignOf_eq hd
    · rw [fam_G, C.slice_height, C.slice_height]

end Choices

/-- the existence sentence of ce:rounding -/
theorem exists_cuspRoundingFamily (h : L.CuspedProjection) : Nonempty (CuspRoundingFamily L) := by
  obtain ⟨C⟩ := L.exists_choices h
  exact ⟨C.witness h⟩

/-- "With no cusps take the constant family": every witness with no cusps is constant -/
theorem _root_.SM.CuspRoundingFamily.eq_of_no_cusps {L : SpatialLink c} (W : CuspRoundingFamily L)
    (h : L.cuspSet = ∅) (lam : ℝ) : W.fam.G lam = L := by
  apply ext'
  funext i t
  apply W.fixed_outside lam i t
  intro k
  exact absurd k.2 (Set.eq_empty_iff_forall_notMem.mp h k.1)

end SpatialLink

/-! ## 6. The row -/

/-- Lemma ce:rounding (row 89). -/
theorem ce_rounding : CeRoundingData where
  exists_family := fun L _ h => L.exists_cuspRoundingFamily h
  smooth_embeddings_start := fun L W =>
    ⟨W.fam.joint_smooth, fun lam => (W.fam.G lam).embedded, fun lam => (W.fam.G lam).regular, W.start⟩
  fixed_outside_disjoint := fun L W =>
    ⟨fun k => ⟨W.a_lt k, W.lt_b k, W.len k⟩, W.intervals_disjoint, W.fixed_outside⟩
  generic_slices := fun L W lam h1 h2 => W.generic lam h1 h2
  clean_no_new_retains := fun L W lam h1 h2 =>
    ⟨W.clean lam h1 h2, W.same_doubles lam h1 h2, fun p q hd =>
      ⟨W.same_velocity lam h1 h2 p q hd, (W.same_data lam h1 h2 p q hd).1,
        (W.same_data lam h1 h2 p q hd).2⟩⟩
  circles_retained := fun L W lam i =>
    ⟨(W.fam.G lam).periodic i, fun t ht => W.fixed_outside lam i t ht⟩
  no_cusps_constant := fun L W h lam => W.eq_of_no_cusps h lam

end

end SM
