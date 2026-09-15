import SM.TransverseFront
import SM.Rounding
import SM.FrontRecordBridge
import SM.FrontGeomModel

/-! # SM ce:rounding — ordinary rounding of the exact cusp germs (FIXED STATEMENT, candidate A)

Source: reference/SM/sm-3-statesum.tex:3029-3058 (statement; the lemma environment closes at 3058),
3059-3170 (proof).  Design memo: work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "89", §5;
statement sketch work/drafts/gap2/Gap2Statements.lean §3-§4 (its vocabulary is reproduced VERBATIM
in §1 below, so that the sibling unit for row 90 ce:smoothing-record and the later row 91 can share
one ported module; the two changes made to the row-89-private structure `CuspRoundingFamily` and the
clause fields added to `CeRoundingData` are listed in §0).  Plan: PLAN_A.md.
Check: `cd work/lean && lake env lean ../drafts/cerounding/Statements_A.lean` (1 sorry = the row).

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

/-- Lemma ce:rounding (row 89). -/
theorem ce_rounding : CeRoundingData := by
  sorry

end

end SM
