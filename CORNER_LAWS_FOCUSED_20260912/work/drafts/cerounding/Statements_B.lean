import SM.TransverseFront
import SM.Rounding
import SM.FrontRecordBridge
import SM.FrontGeomModel

/-! # Row 89 ce:rounding — the fixed statement (architect B, literal spatial reading)

Source: reference/SM/sm-3-statesum.tex:3029-3062 (statement; the lemma environment closes at 3062),
proof 3063-3169.  Design memo: work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §2, §3(d), §4 "89", §5 and
its sketch work/drafts/gap2/Gap2Statements.lean §3-§4 (vocabulary reused VERBATIM except where the
printed text of 89 forces a change; every change is listed in "Changes against the memo" below and in
PLAN_B.md §2).  Main declaration: `SM.ce_rounding : CeRoundingData` (the only `sorry` of this file).

## The printed statement (sm-3:3031-3058, verbatim)

"Let L be a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³,
and write p = (x,z) for its projection. Its only failures of regularity are finitely many isolated
cusps; all other projected coincidences are finitely many transverse double points. Assume there are
no triple points or cusps on another branch, and the two y heights at every double point are
distinct. At every cusp assume the exact germ, on a parameter interval with smooth coordinate
u = y − y₀,
  x = x₀ + A u²,  y = y₀ + u,  z = z₀ + A y₀ u² + (2A/3) u³,  A ≠ 0.          (ce:exact-germ)
The coordinate u may increase or decrease along the prescribed component orientation, which is not
changed. The formula is a hypothesis, not an appeal to a classification of singularities.

There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L, fixed
outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an ordinary
finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and retains every
original crossing with its oriented decorated data. All original parameter circles, component labels
and traversal orientations are retained. With no cusps take the constant family.
This is an ordinary spatial deformation, not asserted Legendrian or positive transverse, and it
carries no self-linking transport statement."

## Printed clause → Lean (hypotheses)

| printed | Lean |
|---|---|
| a smooth oriented spatial embedding of a finite nonempty union of parameter circles in ℝ³ | `L : SpatialLink c`, `0 < c`: `T : Fin c → ℝ → Space`, `C^∞`, 1-periodic (FR-3), jointly injective on the union (`embedded`), nonvanishing derivative (`regular`; an embedding of a compact manifold is an injective immersion); orientation = parameter direction (T-1) |
| write p = (x,z) for its projection | `L.projLoop i = xzOf (L.T i)` (a `SmoothLoop`, so the accepted plain-loop vocabulary `IsDoubleOf`, `occSetOf`, `crossSignOf` applies) |
| its only failures of regularity are finitely many isolated cusps | `IsCusp i t := deriv (xzOf (L.T i)) t = 0`; `cuspSet` (fundamental period) finite: `cusps_finite` ("isolated" is automatic for a finite set) |
| all other projected coincidences are finitely many transverse double points | `doubles_finite`, `transverse` |
| no triple points | `no_triple` |
| or cusps on another branch | a consequence of `transverse` (a cusp has zero projected velocity, so the determinant with it vanishes): `CuspedProjection.not_isCusp_of_isDouble`, PROVED below; not a separate field, so the class stays the memo's |
| the two y heights at every double point are distinct | `heights_distinct` |
| at every cusp the exact germ on a parameter interval with smooth coordinate u = y − y₀ | `exact_germ : ∀ p ∈ cuspSet, ExactCuspGerm p.1 p.2`: `∃ A ≠ 0, ∃ δ > 0` with `y′ ≠ 0` on `(t₀−δ, t₀+δ)` (u a coordinate) and the displayed formula there with `u = y t − y t₀` |
| u may increase or decrease along the prescribed orientation, which is not changed | `y′ ≠ 0` of either sign; the family keeps the parameter (below) |
| the formula is a hypothesis, not an appeal to a classification | `exact_germ` is a field of the hypothesis class |

## Printed clause → Lean (conclusion `CuspRoundingFamily L`, the witness type; row bundle `CeRoundingData`)

| printed | Lean |
|---|---|
| a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings | `fam : SpatialFamily c`: `G : ℝ → SpatialLink c` (each slice embedded and regular), `joint_smooth : ContDiffOn ℝ ∞ (uncurried) (Icc 0 1 ×ˢ univ)` — smoothness and the claim are on `[0,1]`; values outside are irrelevant (the printed proof: "embeddedness outside [0,1] is not claimed") |
| with L_0 = L | `start : fam.G 0 = L` |
| fixed outside disjoint cusp parameter intervals | `a b : L.cuspSet → ℝ`, `a k < t₀ < b k`, `len`, `intervals_disjoint` (disjoint on the circle, i.e. modulo ℤ), `fixed_outside` for every `λ ∈ [0,1]` at every parameter whose orbit avoids the open intervals |
| for every λ > 0 its xz projection is an ordinary finite regular generic diagram | `generic : ∀ λ ∈ (0,1], (fam.G λ).RegularGenericProjection` (regular, finitely many transverse double points, no triple point, heights distinct = the over/under choice by height); the polygonal reading of that diagram (FR-1, `HeightMarking`) is the consumer's hypothesis, not asserted here (GAP-1 closed by design) |
| it cleanly smooths the cusps | `U : L.cuspSet → Set Plane` and `clean : ∀ λ ∈ (0,1], ∃ cs : L.CleanCuspSmoothing (fam.G λ).projLoop, cs.U = U ∧ cs.a = a ∧ cs.b = b` — field for field the accepted `GeomRounding`, with the SAME neighbourhoods and the SAME parameter intervals as the fixing clause (the printed proof: "Each modified portion is one regular embedded oriented arc in a clean cusp neighbourhood") |
| creates no crossing | `creates_no_crossing : IsDoubleOf (fam.G λ).projLoop p q → IsDoubleOf L.projLoop p q` |
| and retains every original crossing | `retains_crossings : IsDoubleOf L.projLoop p q → IsDoubleOf (fam.G λ).projLoop p q` |
| with its oriented decorated data | `same_data`: the over-first tangent-determinant sign and the height order (over = smaller y) are unchanged; the pairing and the cyclic orders are literally unchanged because the double points are the same parameters on the same circles |
| all original parameter circles, component labels and traversal orientations are retained | structural: every slice is a `SpatialLink c` on the same `Fin c` and the same parameter circles, in the same parameter direction (T-1); the family changes only `T` |
| with no cusps take the constant family | `CeRoundingData.const_of_no_cusps`: when `cuspSet = ∅` the constant family `fun _ => L` is a witness |
| this is an ordinary spatial deformation, not asserted Legendrian or positive transverse, and it carries no self-linking transport statement | no contact condition and no `sl` occur in the conclusion (disclaimer; nothing to prove) |

## Changes against the memo's sketch (recorded for the units of rows 90 and 91)

1. `SpatialFamily.joint_smooth`: `ContDiff ℝ ∞` on all of `ℝ × ℝ` → `ContDiffOn ℝ ∞ … (Icc 0 1 ×ˢ univ)`.
   Forced by the printed "0 ≤ λ ≤ 1" and the proof's "embeddedness outside [0,1] is not claimed":
   with `G : ℝ → SpatialLink c` every slice is embedded by type, and the printed construction is
   only shown embedded for `λ ∈ [0,1]` (a global family would need a smooth saturation of `λ`, a
   device foreign to the text).  The syntax `F.G 0 = L`, `(F.G 1).RegularGenericProjection`,
   `HeightMarking (F.G 1) …` of `ContactPathData` / `AmbientIsotopyDescent` is unaffected.
2. `CuspRoundingFamily.intervals_disjoint`: disjointness of the open parameter intervals ON THE
   CIRCLE (`t ∈ Ioo (a k) (b k) → t + n ∉ Ioo (a k') (b k')`), not as subsets of `ℝ` (the memo's
   version admits wrap-around overlaps and is weaker than "disjoint cusp parameter intervals").
3. `CuspRoundingFamily.U` added, and `clean` now produces a `CleanCuspSmoothing` with `cs.U = U`,
   `cs.a = a`, `cs.b = b`: the clean neighbourhoods and the intervals are one datum for the whole
   family and are the intervals of `fixed_outside` (literal reading; the memo let them float with λ).
4. `same_doubles` (an `↔`) split into `creates_no_crossing` and `retains_crossings` (one field per
   printed clause); `fixed_outside`, `generic`, `clean`, … quantified over `λ ∈ [0,1]` / `(0,1]`
   as `∈ Set.Icc` / `∈ Set.Ioc` (printed "0 ≤ λ ≤ 1", "for every λ > 0").
5. `CeRoundingData.const_of_no_cusps` added ("With no cusps take the constant family").
6. `CuspedProjection.not_isCusp_of_isDouble` (proved): the printed "no … cusps on another branch".
`SpatialLink`, `projLoop`, `height`, `IsCusp`, `cuspSet`, `ExactCuspGerm`, `CuspedProjection`,
`RegularGenericProjection`, `CleanCuspSmoothing` are the memo's, verbatim.  `HeightMarking` (rows 90,
91) is not needed by 89 and is not restated here. -/

namespace SM

open Link SmoothFront
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The spatial vocabulary (memo §3, verbatim) -/

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

/-- two spatial links with the same maps are equal (the other fields are proofs) -/
theorem ext' {L L' : SpatialLink c} (h : L.T = L'.T) : L = L' := by
  cases L; cases L'; cases h; rfl

/-- the `xz` projection of component `i`, as a `SmoothLoop` (the plain-loop vocabulary of
SM/FrontRecordBridge.lean §2 applies: `IsDoubleOf`, `occSetOf`, `crossSignOf`) -/
def projLoop (i : Fin c) : SmoothLoop where
  γ := xzOf (L.T i)
  smooth := ((L.smooth i).fst).prodMk ((L.smooth i).snd.snd)
  periodic := fun t => by
    show xzOf (L.T i) (t + 1) = xzOf (L.T i) t
    simp only [xzOf, xOf, zOf, L.periodic i t]

@[simp] theorem projLoop_γ (i : Fin c) : (L.projLoop i).γ = xzOf (L.T i) := rfl

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
  /-- "Its only failures of regularity are finitely many isolated cusps" -/
  cusps_finite : L.cuspSet.Finite
  /-- "At every cusp assume the exact germ" -/
  exact_germ : ∀ p ∈ L.cuspSet, L.ExactCuspGerm p.1 p.2
  /-- "all other projected coincidences are finitely many … double points" -/
  doubles_finite : (occSetOf L.projLoop).Finite
  /-- "… transverse double points" -/
  transverse : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0
  /-- "Assume there are no triple points" -/
  no_triple : ∀ p q r : Fin c × ℝ, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
    IsDoubleOf L.projLoop p r → False
  /-- "and the two y heights at every double point are distinct" -/
  heights_distinct : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q

/-- "no … cusps on another branch": a branch of a double point is never a cusp — a consequence of
transversality (the determinant with a zero velocity vanishes), hence not a separate field -/
theorem CuspedProjection.not_isCusp_of_isDouble (h : L.CuspedProjection) {p q : Fin c × ℝ}
    (hpq : IsDoubleOf L.projLoop p q) : ¬ L.IsCusp p.1 p.2 := by
  intro hc
  apply h.transverse p q hpq
  unfold IsCusp at hc
  rw [hc]
  simp [det]

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

/-- "a permitted smoothed-front diagram: replacing each cusp with one regular embedded oriented arc in
a clean cusp neighbourhood, agreeing with the old germs in endpoint collars and creating no crossing"
(ce:smoothing-record); "every clean ordinary cusp smoothing S(F)" (cp:finite-contact-path); "It
cleanly smooths the cusps" (ce:rounding).  Field for field the accepted `SmoothFront.GeomRounding`
(SM/FrontSmooth.lean §8) on the cusps of `L`'s projection. -/
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

end SpatialLink

/-! ## 2. Families (memo §3, `joint_smooth` on `[0,1]` — change 1) -/

/-- "a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings" (ce:rounding), "a
supplied jointly smooth family of oriented spatial embeddings G_t" (cp:finite-contact-path): each
slice is a `SpatialLink` (embedded, regular); the family is `C^∞` jointly in `(λ, t)` on
`[0,1] × ℝ`.  The values at `λ ∉ [0,1]` carry no claim ("embeddedness outside [0,1] is not
claimed", sm-3:3103-3104). -/
structure SpatialFamily (c : ℕ) where
  G : ℝ → SpatialLink c
  joint_smooth : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (G p.1).T i p.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)

/-! ## 3. Row 89 ce:rounding: the conclusion as a witness structure -/

/-- "There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L,
fixed outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
ordinary finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and
retains every original crossing with its oriented decorated data. All original parameter circles,
component labels and traversal orientations are retained."  One field per printed clause; the last
sentence is structural (every slice is a `SpatialLink c` on the same `Fin c`, the same parameter
circles, in the same parameter direction — the family changes only `T`). -/
structure CuspRoundingFamily {c : ℕ} (L : SpatialLink c) where
  /-- "a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings" -/
  fam : SpatialFamily c
  /-- "with L_0 = L" -/
  start : fam.G 0 = L
  /-- the clean cusp neighbourhoods, one per cusp, for the whole family -/
  U : L.cuspSet → Set Plane
  /-- the cusp parameter intervals `(a k, b k)`, one per cusp … -/
  a : L.cuspSet → ℝ
  b : L.cuspSet → ℝ
  /-- … around the cusp parameter … -/
  a_lt : ∀ k, a k < k.1.2
  lt_b : ∀ k, k.1.2 < b k
  /-- … shorter than the circle … -/
  len : ∀ k, b k - a k < 1
  /-- … "disjoint" (on the circle: no translate of a point of one interval lies in another interval
  of the same circle; intervals on different circles are disjoint by nature) -/
  intervals_disjoint : ∀ k k', k ≠ k' → k.1.1 = k'.1.1 →
    ∀ t ∈ Set.Ioo (a k) (b k), ∀ n : ℤ, t + n ∉ Set.Ioo (a k') (b k')
  /-- "fixed outside disjoint cusp parameter intervals": at every parameter whose orbit avoids the
  open intervals of its circle the family is `L`, for every `λ ∈ [0,1]` -/
  fixed_outside : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ (i : Fin c) (t : ℝ),
    (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (a k) (b k)) →
    (fam.G lam).T i t = L.T i t
  /-- "such that for every λ > 0 its xz projection is an ordinary finite regular generic diagram" -/
  generic : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, (fam.G lam).RegularGenericProjection
  /-- "It cleanly smooths the cusps": for every `λ > 0` the projection is a clean cusp smoothing of
  `L`'s projection in the neighbourhoods `U` on the intervals `(a, b)` (the accepted `GeomRounding`
  shape, field for field) -/
  clean : ∀ lam ∈ Set.Ioc (0 : ℝ) 1,
    ∃ cs : L.CleanCuspSmoothing (fam.G lam).projLoop, cs.U = U ∧ cs.a = a ∧ cs.b = b
  /-- "creates no crossing" -/
  creates_no_crossing : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p q : Fin c × ℝ,
    IsDoubleOf (fam.G lam).projLoop p q → IsDoubleOf L.projLoop p q
  /-- "and retains every original crossing" -/
  retains_crossings : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p q : Fin c × ℝ,
    IsDoubleOf L.projLoop p q → IsDoubleOf (fam.G lam).projLoop p q
  /-- "with its oriented decorated data": the over-first tangent-determinant sign and the height
  order (over = smaller `y`) at every original crossing are unchanged; its pairing and its place in
  the cyclic order of its circle are literally unchanged (same parameters, same circles) -/
  same_data : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    crossSignOf (fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
    ((fam.G lam).height p < (fam.G lam).height q ↔ L.height p < L.height q)

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

theorem a_lt_b (k : L.cuspSet) : R.a k < R.b k := (R.a_lt k).trans (R.lt_b k)

/-- the same double points at every `λ > 0` (the memo's `same_doubles`) -/
theorem isDoubleOf_iff {lam : ℝ} (h : lam ∈ Set.Ioc (0 : ℝ) 1) (p q : Fin c × ℝ) :
    IsDoubleOf (R.fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q :=
  ⟨R.creates_no_crossing lam h p q, R.retains_crossings lam h p q⟩

/-- "All original parameter circles, component labels and traversal orientations are retained":
every slice lives on the same circles with the same parameter (structural; recorded as a theorem) -/
theorem same_circles (lam : ℝ) (i : Fin c) : Function.Periodic ((R.fam.G lam).T i) 1 :=
  (R.fam.G lam).periodic i

end CuspRoundingFamily

/-- **ce:rounding (row 89).**  `exists_family` is the existence sentence for every `L` of the
printed class (a nonempty finite union of circles: `0 < c`); `const_of_no_cusps` is "With no cusps
take the constant family".  The closing disclaimer ("an ordinary spatial deformation, not asserted
Legendrian or positive transverse, … no self-linking transport statement") is the absence of any
contact condition or `sl` in `CuspRoundingFamily`. -/
structure CeRoundingData : Prop where
  /-- "There is a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L,
  fixed outside disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an
  ordinary finite regular generic diagram. It cleanly smooths the cusps, creates no crossing, and
  retains every original crossing with its oriented decorated data. All original parameter circles,
  component labels and traversal orientations are retained." -/
  exists_family : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    Nonempty (CuspRoundingFamily L)
  /-- "With no cusps take the constant family." -/
  const_of_no_cusps : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    L.cuspSet = ∅ → ∃ R : CuspRoundingFamily L, ∀ lam : ℝ, R.fam.G lam = L

/-- Lemma ce:rounding (sm-3:3029-3062).  The only `sorry` of this file; proved in Skeleton_B.lean
from the chain of leaves. -/
theorem ce_rounding : CeRoundingData := by
  sorry

end

end SM
