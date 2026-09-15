import SM.TransverseFront
import SM.Rounding
import SM.CornerStateSum
import SM.UniformDefinition
import SM.PolynomialBlock
import SM.FrontRecordBridge

/-! # GAP-2 statement-only rows: statable bundles (design sketch, 2026-09-14)

Companion of work/drafts/gap2/GAP2_STATEMENTS_MEMO.md.  Every declaration here is a `structure`, a
`def` or an `abbrev`; there is NO theorem, NO `sorry`, NO `axiom`.  The `… Data : Prop` bundles are
the proposed FIXED STATEMENTS of the rows blocked by GAP-2 (ambient isotopy ⇒ `LinkEquiv`, outside
scope by design D2) so that they can be STATED and reported "stated, unproved, blocked by GAP-2".
Nothing here is to be ported to work/lean without the row's own statement review.

Rows covered: 89 ce:rounding, 90 ce:smoothing-record, 91 cp:finite-contact-path, 94 fd:contact,
99 cf:thm-carrierfloor (R)(A)(B)(C), 100 thm:floor, 155 CV:thm:carrierfloor (R)(A)(B)(C) by the
polygon bridge, 161 CV:ax:etnyre + 162 CV:ax:slbound (the composite writhe form). -/

namespace SM

open Link SmoothFront
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. FR-1 for transverse fronts: a polygonal `Diagram` carrying the record of a
`SmoothKnotDiagram` (over = the diagram's own `isOver`, i.e. smaller `y`).  The analogue of the
accepted `Carried` (SM/Rounding.lean §4) and `RecordCarried` (curl lane) for the accepted class of
def:transverse-front; "the original campaign polynomial of this actual diagram `D_T`" (fd:contact)
is `P X` for any such `X` (well defined by rp:record-polynomial). -/

/-- record-level carrying of the polygonal one-component diagram `X` by the smooth knot diagram `D` -/
structure SmoothKnotDiagram.Carries (D : SmoothKnotDiagram) (X : Diagram) where
  /-- one parameter circle -/
  one : X.Γ.c = 1
  /-- the parameter (in the fundamental period) at which the occurrence `v` is traversed -/
  τ : X.Γ.Visit → ℝ
  τ_mem : ∀ v, τ v ∈ Set.Ico (0 : ℝ) 1
  τ_inj : Function.Injective τ
  /-- the two occurrences of a crossing are the two parameters of one double point of `D` -/
  twin_double : ∀ v, D.IsDouble (τ v) (τ (X.twin v))
  /-- every double point of `D` is one of the crossings -/
  doubles : ∀ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 → t ∈ Set.Ico (0 : ℝ) 1 → D.IsDouble s t →
    ∃ v : X.Γ.Visit, s = τ v ∧ t = τ (X.twin v)
  /-- the cyclic order of the occurrences along the oriented circle is `X`'s -/
  order : ∀ v w z : X.Γ.Visit,
    (cycBetween (τ v) (τ w) (τ z) ↔ cycBetween (X.visitCoord v) (X.visitCoord w) (X.visitCoord z))
  /-- the over/under assignment is `D`'s: the over visit of `X` is the over branch of `D` -/
  over_eq : ∀ x : X.Γ.Crossing, D.isOver (τ (X.overVisit x)) (τ (X.underVisit x))
  /-- the signs agree: `X.sign = sgn det_xz(u_O, u_U)` of `D` -/
  sign_eq : ∀ x : X.Γ.Crossing,
    (X.sign x : ℤ) = D.crossSign (τ (X.overVisit x)) (τ (X.underVisit x))

/-! ## 2. Row 94 fd:contact (sm-3:3404-3430).  `sl` is NOT in the accepted layer (SM defines it as the
framed linking number fd:framed-linking, rem:sl-convention; the CV text never defines it).  The bundle
therefore takes `sl` as an EXPLICIT PARAMETER — no opaque constant, no sixth axiom — and the sl-free
writhe form (the composite the consumer cf:thm-carrierfloor (C) uses) is stated separately. -/

/-- fd:contact with `sl` a parameter (to be instantiated by `SM.sl` of fd:framed-linking when the fd
block 84-88 exists).  Field `over_rule_sign` is the first printed sentence (definitional on the
accepted class); `front_writhe` is display fd:front-writhe; `representative_bound` is display
fd:representative-bound on "an individual smooth positive transverse knot whose specified xz
projection D_T is an ordinary finite regular generic diagram" — every `TransverseKnot` (def:transverse-
front), read polygonally through `Carries` (FR-1). -/
structure FdContactData (sl : TransverseKnot → ℤ) : Prop where
  /-- "In the xz front page the smaller-y branch is over, and its crossing sign is
  sgn det_xz(u_O, u_U)" -/
  over_rule_sign : ∀ (K : TransverseKnot) (s t : ℝ), K.front.IsDouble s t →
    (K.front.isOver s t ↔ yOf K.T s < yOf K.T t) ∧
    K.front.crossSign s t = ((SignType.sign (det (K.front.vel s) (K.front.vel t)) : SignType) : ℤ)
  /-- fd:front-writhe: `sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))` -/
  front_writhe : ∀ K : TransverseKnot, sl K = K.front.writhe
  /-- fd:representative-bound: `sl(T) ≤ −max deg_a P_T(a,z) − 1` -/
  representative_bound : ∀ (K : TransverseKnot) (X : Diagram), K.front.Carries X →
    sl K ≤ -degAZ (P X) - 1

/-- The sl-free form of fd:contact — the conjunction of its two displays with `sl` eliminated; this is
exactly what cf:thm-carrierfloor (C) consumes ("sl(K_T) = w(T)" then "max deg_a P_{D̄} ≤ −sl(K_T) − 1").
Statable NOW on the accepted layer. -/
structure TransverseFrontBoundData : Prop where
  writhe_bound : ∀ (K : TransverseKnot) (X : Diagram), K.front.Carries X →
    K.front.writhe ≤ -degAZ (P X) - 1

/-! ## 3. Rows 89-91: the smooth spatial vocabulary (finite unions of parameter circles embedded in
`ℝ³`, cusped `xz` projections with the exact germ, clean cusp smoothings, height markings). -/

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
field the accepted `GeomMarking` (SM/FrontGeomModel.lean) with `slopeOf G` replaced by `L.height`. -/
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
(ce:smoothing-record); "every clean ordinary cusp smoothing S(F)" (cp:finite-contact-path).  Field for
field the accepted `SmoothFront.GeomRounding` (SM/FrontSmooth.lean) on the cusps of `L`'s projection. -/
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

/-- "a jointly smooth family of oriented spatial embeddings" `G_t` (cp:finite-contact-path), each slice
a `SpatialLink` (embedded, regular) -/
structure SpatialFamily (c : ℕ) where
  G : ℝ → SpatialLink c
  joint_smooth : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (G p.1).T i p.2)

/-! ## 4. Row 89 ce:rounding (sm-3:3029-3062): the conclusion as a witness structure. -/

/-- "a jointly smooth family L_λ, 0 ≤ λ ≤ 1, of oriented spatial embeddings with L_0 = L, fixed outside
disjoint cusp parameter intervals, such that for every λ > 0 its xz projection is an ordinary finite
regular generic diagram. It cleanly smooths the cusps, creates no crossing, and retains every original
crossing with its oriented decorated data. All original parameter circles, component labels and
traversal orientations are retained." -/
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

/-- ce:rounding (row 89): the existence sentence.  Provable in principle (no interface obstacle);
not blocked by GAP-2 itself — only its consumer 91 is. -/
structure CeRoundingData : Prop where
  exists_family : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    Nonempty (CuspRoundingFamily L)

/-! ## 5. Row 90 ce:smoothing-record (sm-3:3171-3187). -/

/-- "Every such actual diagram has the same named decorated record as the diagram D_ε = p(L_1) of the
lemma, including crossing-free components. Consequently their source values F_D(l,m) and campaign
polynomials P_D(a,z) agree."  Stated between any two clean smoothings (D_ε is one of them). -/
structure CeSmoothingRecordData : Prop where
  record_iso : ∀ {c : ℕ} (L : SpatialLink c), L.CuspedProjection →
    ∀ (G G' : Fin c → SmoothLoop) (S S' : Diagram),
      Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.CleanCuspSmoothing G') →
      Nonempty (L.HeightMarking G S) → Nonempty (L.HeightMarking G' S') →
      Nonempty (RecordIso S.record S'.record)
  polynomials_agree : ∀ {c : ℕ} (L : SpatialLink c), L.CuspedProjection →
    ∀ (G G' : Fin c → SmoothLoop) (S S' : Diagram),
      Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.CleanCuspSmoothing G') →
      Nonempty (L.HeightMarking G S) → Nonempty (L.HeightMarking G' S') →
      lmF S = lmF S' ∧ P S = P S'

/-! ## 6. Row 91 cp:finite-contact-path (sm-3:3210-3230) — THE GAP-2 ROW. -/

/-- "Suppose a supplied jointly smooth family of oriented spatial embeddings G_t starts at this
parametrized L and ends at T, whose specified xz projection D_T is an ordinary finite regular generic
diagram. Then every clean ordinary cusp smoothing S(F), with smaller y over at the unchanged crossings,
has the same campaign polynomial as D_T: P_{S(F)} = P_{D_T}." -/
structure ContactPathData : Prop where
  endpoint_polynomial : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (F : SpatialFamily c), F.G 0 = L → (F.G 1).RegularGenericProjection →
    ∀ (X : Diagram), Nonempty ((F.G 1).HeightMarking (F.G 1).projLoop X) →
    ∀ (G : Fin c → SmoothLoop) (S : Diagram),
      Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.HeightMarking G S) →
      P S = P X

/-- GAP-2 made explicit: the missing descent clause "an ambient isotopy of the actual oriented links
gives equal H" (the printed proof's "The retained global source premise yields H_{D_ε} = H_{D_T}").
On the accepted layer this reads: the polygonal readings of the two ends of a smooth spatial family
with regular generic projections are `LinkEquiv` — i.e. Reidemeister's theorem for smooth isotopies,
EXCLUDED by design D2 (SM/LinkInterfaces.lean header; `HomflyClauses.descent` is over `LinkEquiv`).
This is a `def` of a `Prop`, NOT an axiom, recorded so the report can name what is missing. -/
def AmbientIsotopyDescent : Prop :=
  ∀ {c : ℕ} (F : SpatialFamily c),
    (F.G 0).RegularGenericProjection → (F.G 1).RegularGenericProjection →
    ∀ X₀ X₁ : Diagram,
      Nonempty ((F.G 0).HeightMarking (F.G 0).projLoop X₀) →
      Nonempty ((F.G 1).HeightMarking (F.G 1).projLoop X₁) →
      LinkEquiv X₀ X₁

/-! ## 7. Row 99 cf:thm-carrierfloor (sm-3:4282-4330), clauses (R), (A), (B), (C). -/

/-- "after reversing the orientation if necessary, either every principal turn is positive, or exactly
one is negative and every other is positive" (reversal negates every principal turn) -/
def UniformOrOneDissent (C : PolyComp) : Prop :=
  (∀ i, 0 < principalTurn C.P i) ∨
  (∃ i, principalTurn C.P i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn C.P j) ∨
  (∀ i, principalTurn C.P i < 0) ∨
  (∃ i, 0 < principalTurn C.P i ∧ ∀ j, j ≠ i → principalTurn C.P j < 0)

/-- (A) the rounding record `Round(L, D, ε) = (L_ε, D_ε)`: the accepted named construction of
cf:lem-rounding (`CornerRounding.roundedWitness`), a FUNCTION of the data — "one curve and one diagram
at those data" -/
def Round (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    RoundingWitness C D ε :=
  CornerRounding.roundedWitness h

/-- Clause (R): "Let D be an oriented knot diagram and −D the same diagram with every arrow reversed.
Then P_{−D} = P_D; consequently an oriented knot and its reverse have the same polynomial. Moreover −D
has the same crossing signs and the same writhe as D, and the rotation of its underlying plane curve is
the negative of that of D."  Provable now (lp:coefficient-transport + `ReverseCarries`); not GAP-2. -/
structure CarrierFloorRData : Prop where
  P_reverse : ∀ X : Diagram, X.componentCount = 1 → P X.reverse = P X
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  rot_reverse_polygon : ∀ (C : PolyComp), Regular C.P →
    rotationNumber (reversal C.P) = - rotationNumber C.P
  rot_reverse_curve : ∀ γ : ClosedC1Curve, γ.reverse.rot = - γ.rot

/-- Clause (A): the record is one curve and one diagram at those data; the junction at a corner is
determined by ε, the two incident unit directions and the fixed profile; the rest of the curve is L. -/
structure CarrierFloorAData : Prop where
  /-- one record at the data -/
  one_record : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h h' : CornerRounding.Admissible C D ε), Round C D ε h = Round C D ε h'
  /-- `D_ε` is `D` -/
  diagram_eq : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    Nonempty (Carried (Round C D ε h).Lε D.toDiagram)
  /-- the junction at corner `j` depends only on `ε`, the corner and the two incident unit directions -/
  junction_local : ∀ (C C' : PolyComp) (D : PolygonDiagram C) (D' : PolygonDiagram C') (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (h' : CornerRounding.Admissible C' D' ε)
    (j : ℕ) (j' : ℕ), j < C.k → j' < C'.k →
    C.P j = C'.P j' → CornerRounding.uDir C j = CornerRounding.uDir C' j' →
    CornerRounding.vDir C j = CornerRounding.vDir C' j' →
    (Round C D ε h).Lε.γ '' Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) =
      (Round C' D' ε h').Lε.γ '' Set.Icc ((Round C' D' ε h').a j') ((Round C' D' ε h').b j')
  /-- the rest of the curve is `L` -/
  rest_is_L : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε)
    (p : Plane), p ∉ (⋃ i, cornerDisc C ε i) → (p ∈ Set.range (Round C D ε h).Lε.γ ↔ p ∈ polygonImage C)

/-- Clause (B): "there are a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁) the rounded
curve L_ε of the record Round(L, D, ε) has exactly R points at which its unit tangent equals u and
exactly R at which it equals −u; at each of them the tangent crosses that direction in the positive
sense."  Provable now (plane geometry: lem:uniformrot + the junction lifts); not GAP-2. -/
structure CarrierFloorBData : Prop where
  tangencies : ∀ (C : PolyComp) (D : PolygonDiagram C), (∀ i, principalTurn C.P i ≠ 0) →
    UniformOrOneDissent C →
    ∃ (u : Plane) (ε₁ : ℝ), euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ CornerRounding.clearance C ∧
      ∀ (ε : ℝ) (h : CornerRounding.Admissible C D ε), ε < ε₁ →
        (({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ (Round C D ε h).T t = u}.ncard : ℝ) = |rotationNumber C.P|) ∧
        (({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ (Round C D ε h).T t = -u}.ncard : ℝ) = |rotationNumber C.P|) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) 1, ((Round C D ε h).T t = u ∨ (Round C D ε h).T t = -u) →
          ∃ j, j < C.k ∧ t ∈ Set.Ioo ((Round C D ε h).a j) ((Round C D ε h).b j) ∧
            0 < deriv ((Round C D ε h).θ j) t)

/-- the hypotheses of clause (C) on a knot diagram `X` whose underlying plane curve is the polygon `C`:
all crossings positive; principal turns existing (`Regular`, in `X.generic`), nonzero, of magnitude
below π; finitely many transverse double points, no triple points, none a corner, no corner on a
non-incident edge (all in `(Shadow.single C).Generic` = `X.generic` after `shadow`); the
uniform/one-dissent alternative after reversal -/
structure CarrierFloorCHyp (C : PolyComp) (X : Diagram) : Prop where
  shadow : X.Γ = Shadow.single C
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  turn_ne : ∀ i, principalTurn C.P i ≠ 0
  turn_lt_pi : ∀ i, |principalTurn C.P i| < Real.pi
  alternative : UniformOrOneDissent C

/-- Clause (C): "min deg_a P_D(a,z) ≥ 1 − w − R, and the same bound holds for f_D(a) = [z⁰]P_D(a,z)
whenever f_D ≠ 0" — the second sentence in support form (every present monomial `a^d z^k` has
`d ≥ 1 − w − R`, which covers `f_D`'s support).  BLOCKED BY GAP-2 (through fd:contact) — and by
cf:lem-curl (98, in progress), the transverse lift construction and the mirror identity
`P_{D̄}(a,z) = P_D(a⁻¹, −z)` (all provable). -/
structure CarrierFloorCData : Prop where
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  floor_support : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ∀ d k : ℤ, coeffAt d k (P X) ≠ 0 → ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (d : ℝ)

/-! ## 8. Row 100 thm:floor (sm-3:4576-4590). -/

section Floor

open Carrier

variable {n : ℕ} [NeZero n]

/-- "after possibly reversing its orientation either all turns are left, or exactly one turn is right"
on the subpolygon `Q` of the decomposition `S` (uniform = `CarrierUniform`; one dissent = one turn of
the opposite sign) -/
def CarrierUniformOrOneDissent (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  CarrierUniform hn hP S q ∨
  ∃ τ : SignType, τ ≠ 0 ∧ ∃ j₀, turn (ccpCornerPolygon hn hP S q) j₀ = -τ ∧
    ∀ j, j ≠ j₀ → turn (ccpCornerPolygon hn hP S q) j = τ

/-- thm:floor: "min deg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q, H⁺_Q ∈ ℤ[a^{±1}, z²], so min deg_z H⁺_Q ≥ 0".
`H⁺_Q = cornerHomfly`, `d_Q = cornerSlot` (def:C, accepted).  The `a`-floor is BLOCKED BY GAP-2
(through cf:thm-carrierfloor (C)); the `z`-parity clause is provable now (lp:core knot support). -/
structure FloorTheoremData : Prop where
  a_floor : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS)
  z_parity : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS)

end Floor

end

end SM

/-! ## 9. CV lane: rows 161 CV:ax:etnyre and 162 CV:ax:slbound (d10_axioms.tex:387-420). -/

namespace CV

open SM SM.Link

/-- The printed pair with `sl` an EXPLICIT PARAMETER (the CV text never defines `sl`; no constant is
introduced).  `etnyre`: "Let T be a front diagram of a transverse knot with no downward vertical
tangency. Then sl(T) equals the writhe of T" — on the accepted class every vertical tangent points
upward (`vertical_up`), so the hypothesis is automatic.  `slbound`: "sl(T) ≤ −max deg_a P_T(a,z) − 1",
`P_T` the HOMFLY–PT polynomial of the knot `T` presents = `homfly X` for a diagram `X` carrying the
front (FR-1), on the accepted class of transverse knots WITH a generic front (SM fd:contact's domain;
a narrowing of the CV axiom's "Let T be a transverse knot", recorded). -/
structure SlBoundData (sl : TransverseKnot → ℤ) : Prop where
  etnyre : ∀ K : TransverseKnot, sl K = K.front.writhe
  slbound : ∀ (K : TransverseKnot) (X : Diagram), K.front.Carries X →
    sl K ≤ -degAZ (homfly X) - 1

/-- The used consequence — the bridge "the diagram's writhe is the quantity bounded by ax:slbound" —
the one statement CV:thm:carrierfloor (C) consumes from the pair.  Statable now; = SM
`TransverseFrontBoundData` with `homfly` for `P` (`P_eq_homfly`). -/
structure TransverseFrontBoundData : Prop where
  writhe_bound : ∀ (K : TransverseKnot) (X : Diagram), K.front.Carries X →
    K.front.writhe ≤ -degAZ (homfly X) - 1

end CV
