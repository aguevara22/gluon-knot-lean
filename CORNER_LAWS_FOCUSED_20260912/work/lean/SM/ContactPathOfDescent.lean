-- Ported 10:49Z 2026-09-14 from work/drafts/gap2/CPRow91_Skeleton.lean (row 91 modulo the descent clause; architect unit) by the pod executor; body verbatim except one docstring sentence on the clause's scope corrected after the statement review (FR-CP-7). LIBRARY MATERIAL: the theorem SM.cp_finite_contact_path_of_descent is conditional on the Prop SM.AmbientIsotopyDescent (GAP-2).
-- Header updated 22:40Z 2026-09-15 by the pod executor (comment only; no declaration changed): since 2026-09-15 the descent clause is asserted by the registered literature axiom SM.lit_homfly_descent : AmbientIsotopyDescent (SM/LitHomflyDescent.lean, policy label "lit:homfly (descent sentence)", the author's GAP-2 decision, work/AUTHOR_NOTES.md), and row 91 cp:finite-contact-path IS mapped and accepted as SM.cp_finite_contact_path (SM/ContactPath.lean) := cp_finite_contact_path_of_descent lit_homfly_descent. The docstrings below that call AmbientIsotopyDescent "a def : Prop, not an axiom" remain literally true of the predicate itself; the assumption lives in the separate axiom declaration.
import SM.CeRounding

/-! # Row 91 cp:finite-contact-path — statement and proof skeleton "modulo the descent clause"

Draft, 2026-09-14 (pod, architect subagent of the executor; lane "Row 91 modulo the descent clause",
AUTHOR_NOTES ~10:02Z).  Companion plan: work/drafts/gap2/CPRow91_PLAN.md.  Design memo:
work/drafts/gap2/GAP2_STATEMENTS_MEMO.md §1, §3(d), §4 "91", §6.  Nothing here is to be ported
before a statement review; a conditional row theorem is library material (D-F11/D-F14) and is never
mapped as implemented unless GAP-2 closes.  (GAP-2 CLOSED 2026-09-15 — by the author's decision D-GAP2, not
by proof: the descent clause is asserted by the registered literature axiom `SM.lit_homfly_descent :
AmbientIsotopyDescent` in SM/LitHomflyDescent.lean, and row 91 is accepted as `SM.cp_finite_contact_path`
in SM/ContactPath.lean; see the header lines above.)

Source: reference/SM/sm-3-statesum.tex:3210-3233 (statement), 3234-3326 (proof).  Inputs, both
ACCEPTED on the shared vocabulary: row 90 ce:smoothing-record = SM/CeSmoothingRecord.lean
(`SpatialLink`, `CuspedProjection`, `RegularGenericProjection`, `HeightMarking`, `CleanCuspSmoothing`
with `collar`, `SpatialFamily`, `CuspRoundingFamily`, `SM.ce_smoothing_record`) and row 89 ce:rounding
= SM/CeRounding.lean (`CuspRoundingWitness`, `SM.ce_rounding`).  Also consumed: `presentations`
(rp:record-polynomial), `P_eq_homfly` (lp:core), `homfly_descent` (lit:homfly's fifth clause over
`LinkEquiv`, design D2).

## The printed statement (sm-3:3212-3231, verbatim)

"Let C be a finite nonempty disjoint union of oriented parameter circles, and let L : C → ℝ³ be a
smooth embedding with nonvanishing parameter derivative. Assume its xz projection F is regular except
at finitely many cusps, each with the exact germ [cp:exact-cusp]. Assume the only multiple points of
F are finitely many transverse double points, none at a cusp, and the two y values differ at every
double point. Suppose a supplied jointly smooth family of oriented spatial embeddings G_t starts at
this parametrized L and ends at T, whose specified xz projection D_T is an ordinary finite regular
generic diagram. Then every clean ordinary cusp smoothing S(F), with smaller y over at the unchanged
crossings, has the same campaign polynomial as D_T: P_{S(F)} = P_{D_T} [cp:endpoint-polynomial]. No
contact condition is imposed on G_t or on the rounding family."

## Printed clause → field of `ContactPathData`

| tex lines | printed | field |
|---|---|---|
| 3212-3214 | "Let C be a finite nonempty disjoint union of oriented parameter circles, and let L : C → ℝ³ be a smooth embedding with nonvanishing parameter derivative." | `link_class` (`L : SpatialLink c`, `0 < c`) |
| 3214-3219 | "Assume its xz projection F is regular except at finitely many cusps, each with the exact germ" | `cusped_front` |
| 3220-3222 | "Assume the only multiple points of F are finitely many transverse double points, none at a cusp, and the two y values differ at every double point." | `double_points` |
| 3222-3225 | "Suppose a supplied jointly smooth family of oriented spatial embeddings G_t starts at this parametrized L and ends at T, whose specified xz projection D_T is an ordinary finite regular generic diagram." | `supplied_family` |
| 3225-3227 | "every clean ordinary cusp smoothing S(F), with smaller y over at the unchanged crossings" | `smaller_y_over` |
| 3227-3230 | "has the same campaign polynomial as D_T: P_{S(F)} = P_{D_T}" | `endpoint_polynomial` (THE theorem; needs the descent clause) |
| 3231 | "No contact condition is imposed on G_t or on the rounding family." | no field (asserts nothing; the hypotheses mention no `contactForm`) |

## The gap and its rendering (§1)

The printed proof (3234-3326) has exactly one step outside the frozen interfaces: "Thus its endpoint
gives an actual ambient isotopy between the two oriented links. The retained global source premise
yields H_{D_ε} = H_{D_T}" (3310-3312), consuming lit:homfly's fifth clause "Its value depends only on
the oriented link presented by D".  The accepted `SM.lit_homfly` renders that clause as
`HomflyClauses.descent : LinkEquiv D D' → H D = H D'` — descent to the equivalence generated by planar
isotopy and the three moves (design D2: Reidemeister's theorem is outside the formal scope and is admitted
as no axiom; the 2026-09-15 axiom `SM.lit_homfly_descent` is the printed descent sentence itself — the second
declaration of lit:homfly, five literature interfaces, six axiom constants — not Reidemeister's theorem).  The
step needs descent along a SMOOTH SPATIAL isotopy of the links whose projections the two
polygonal diagrams read.  We name that clause `AmbientIsotopyDescent` (a `def … : Prop`; the predicate itself is not an
axiom — since 2026-09-15 it is ASSERTED by the registered literature axiom `SM.lit_homfly_descent :
AmbientIsotopyDescent` in SM/LitHomflyDescent.lean, policy label "lit:homfly (descent sentence)", the
author's decision D-GAP2) and prove the row from it: `cp_finite_contact_path_of_descent :
AmbientIsotopyDescent → ContactPathData`.
The memo's `LinkEquiv` form is kept as `AmbientIsotopyLinkEquiv` (Reidemeister's theorem proper) and
shown to imply it; the printed proof's own split — isotopy extension (3276-3312, proved in the text)
+ the literature premise on an AMBIENT isotopy — is recorded as `IsotopyExtension` and
`AmbientIsotopyDescentLit`, whose conjunction also implies it.

## Route (the printed proof, 3234-3326)

* §2 the concatenated family (3259-3268): `H_s = L_{1−η(2s)}` for `s ≤ 1/2`, `G_{η(2s−1)}` for
  `s ≥ 1/2`, `η = Real.smoothTransition` (the printed η: smooth, 0 at 0, 1 at 1, flat at both ends).
  Both halves are jointly smooth on all of `ℝ × ℝ`, and each is the constant `L` on its closed side of
  the join, so `H = A + B − L` as maps into `ℝ³` — joint smoothness at the join is a sum, not a
  one-sided derivative computation (`SpatialFamily.glue`).
* §3 the polygonal reading of `D_ε = p(L_1)` (3247-3255, "The two actual diagrams S(F) and D_ε have
  identical named decorated records"): the reading `S` of the clean smoothing `S(F)` is transported
  to a reading of `p(L_1)` (`HeightMarking.toSmoothing`, the inverse of the accepted `ofSmoothing`;
  `toHeightOrder`, the inverse of the accepted `ofHeightOrder`) — so `D_ε` HAS a polygonal reading
  (`S` itself) and no existence of carriers is asserted (FR-1).
* §4 `P_{S(F)} = P_{D_ε}` by the accepted row 90 (`ce_smoothing_record.source_and_polynomial`), and
  `P_{D_ε} = P_{D_T}` by the descent clause on the concatenated family plus lp:core (`P_eq_homfly`).
* §5 the row: rounding family from the accepted row 89, the fields, the theorem. -/

namespace SM

open Link SmoothFront
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. Statements: the row bundle and the descent clauses -/

/-- Lemma cp:finite-contact-path (sm-3:3210-3233), one field per printed clause (table in the module
docstring).  Throughout: "C … oriented parameter circles, L : C → ℝ³ a smooth embedding with
nonvanishing parameter derivative" is `L : SpatialLink c` with `0 < c` ("nonempty"; orientation =
parameter direction, T-1); "its xz projection F" is `L.projLoop` with cusps `L.cuspSet`; the two
"Assume" sentences are `L.CuspedProjection` (the class of ce:rounding, sm-3:3033-3042, identical
clauses); "a supplied jointly smooth family of oriented spatial embeddings G_t" is `F : SpatialFamily c`
(indexed by all of `ℝ`, every slice embedded and regular) with `F.G 0 = L` ("starts at this
parametrized L") and `T = F.G 1`; "whose specified xz projection D_T is an ordinary finite regular
generic diagram" is `(F.G 1).RegularGenericProjection` read polygonally (FR-1) by
`(F.G 1).HeightMarking (F.G 1).projLoop X` (over = smaller `y` of `T`, the specified diagram's own
height choice); "every clean ordinary cusp smoothing S(F)" is a loop family `G` with
`L.CleanCuspSmoothing G` (row 90's definition sentence) read polygonally by `L.HeightMarking G S`,
whose `over_iff` IS "with smaller y over at the unchanged crossings"; `P` is the accepted campaign
polynomial (SM/LocalPolynomial.lean).  Fields 1-5 are the printed hypotheses read back on the
vocabulary (the pattern of the accepted `CeRoundingData`); `endpoint_polynomial` is the theorem. -/
structure ContactPathData : Prop where
  /-- sm-3:3212-3214: "Let C be a finite nonempty disjoint union of oriented parameter circles, and
  let L : C → ℝ³ be a smooth embedding with nonvanishing parameter derivative." -/
  link_class : ∀ {c : ℕ} (L : SpatialLink c), 0 < c →
    (∀ i, ContDiff ℝ ∞ (L.T i)) ∧ (∀ i, Function.Periodic (L.T i) 1) ∧
    (∀ (i j : Fin c) (s t : ℝ), L.T i s = L.T j t → i = j ∧ SameT s t) ∧
    (∀ i t, deriv (L.T i) t ≠ 0)
  /-- sm-3:3214-3219: "Assume its xz projection F is regular except at finitely many cusps, each with
  the exact germ [cp:exact-cusp]" (= ce:exact-germ, `ExactCuspGerm`). -/
  cusped_front : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    L.cuspSet.Finite ∧ (∀ p ∈ L.cuspSet, L.ExactCuspGerm p.1 p.2)
  /-- sm-3:3220-3222: "Assume the only multiple points of F are finitely many transverse double
  points, none at a cusp, and the two y values differ at every double point." ("none at a cusp" is a
  consequence of transversality, `CuspedProjection.not_isCusp_of_isDouble`, CE-R3.) -/
  double_points : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    (occSetOf L.projLoop).Finite ∧
    (∀ p q : Param c, IsDoubleOf L.projLoop p q →
      det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0) ∧
    (∀ p q r : Param c, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
      IsDoubleOf L.projLoop p r → False) ∧
    (∀ p q : Param c, IsDoubleOf L.projLoop p q → ¬ L.IsCusp p.1 p.2) ∧
    (∀ p q : Param c, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q)
  /-- sm-3:3222-3225: "Suppose a supplied jointly smooth family of oriented spatial embeddings G_t
  starts at this parametrized L and ends at T, whose specified xz projection D_T is an ordinary
  finite regular generic diagram.": joint `C^∞` smoothness, every slice embedded and regular on the
  same parameter circles, `G_0 = L` as parametrized maps, and the end's projection has no cusp and
  finitely many transverse double points, no triple point, distinct heights. -/
  supplied_family : ∀ {c : ℕ} (L : SpatialLink c) (F : SpatialFamily c), F.G 0 = L →
    (F.G 1).RegularGenericProjection →
    (∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (F.G p.1).T i p.2)) ∧
    (∀ (t : ℝ) (i j : Fin c) (s s' : ℝ), (F.G t).T i s = (F.G t).T j s' → i = j ∧ SameT s s') ∧
    (∀ (t : ℝ) (i : Fin c) (s : ℝ), deriv ((F.G t).T i) s ≠ 0) ∧
    (∀ (t : ℝ) (i : Fin c), Function.Periodic ((F.G t).T i) 1) ∧
    (∀ i, (F.G 0).T i = L.T i) ∧
    (F.G 1).cuspSet = ∅ ∧ (occSetOf (F.G 1).projLoop).Finite ∧
    (∀ p q : Param c, IsDoubleOf (F.G 1).projLoop p q →
      det (deriv (xzOf ((F.G 1).T p.1)) p.2) (deriv (xzOf ((F.G 1).T q.1)) q.2) ≠ 0) ∧
    (∀ p q r : Param c, IsDoubleOf (F.G 1).projLoop p q → IsDoubleOf (F.G 1).projLoop q r →
      IsDoubleOf (F.G 1).projLoop p r → False) ∧
    (∀ p q : Param c, IsDoubleOf (F.G 1).projLoop p q → (F.G 1).height p ≠ (F.G 1).height q)
  /-- sm-3:3225-3227: "every clean ordinary cusp smoothing S(F), with smaller y over at the unchanged
  crossings": a clean smoothing keeps exactly the crossings of `F` ("unchanged"), and its polygonal
  reading puts the smaller-`y` branch of `L` over at each of them. -/
  smaller_y_over : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (G : Fin c → SmoothLoop) (S : Diagram) (r : L.CleanCuspSmoothing G)
      (m : L.HeightMarking G S),
      (∀ p q : Param c, IsDoubleOf G p q ↔ IsDoubleOf L.projLoop p q) ∧
      (∀ k : L.cuspSet, ∀ t ∈ Set.Ioo (r.a k) (r.b k), ∀ q : Param c, ¬ SameParam (k.1.1, t) q →
        (G q.1).γ q.2 ≠ (G k.1.1).γ t) ∧
      ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
        (S.overBit (m.Φ p) = true ↔ L.height p.1 < L.height q.1)
  /-- sm-3:3227-3230, display cp:endpoint-polynomial: "has the same campaign polynomial as D_T:
  P_{S(F)} = P_{D_T}" — for every polygonal reading `X` of `D_T` and every polygonal reading `S` of a
  clean smoothing.  (The rendering of the GAP-2 memo §4 "91", unchanged.) -/
  endpoint_polynomial : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    ∀ (F : SpatialFamily c), F.G 0 = L → (F.G 1).RegularGenericProjection →
    ∀ (X : Diagram), Nonempty ((F.G 1).HeightMarking (F.G 1).projLoop X) →
    ∀ (G : Fin c → SmoothLoop) (S : Diagram),
      Nonempty (L.CleanCuspSmoothing G) → Nonempty (L.HeightMarking G S) →
      P S = P X

/-- **GAP-2, the missing clause** — what the printed proof consumes at sm-3:3276-3312, namely the literature premise it invokes at 3310-3312 together with the isotopy-extension step it performs by hand at 3276-3312 (the split is `ambientIsotopyDescent_of_lit` below; review of 2026-09-14, FR-CP-7) ("Thus
its endpoint gives an actual ambient isotopy between the two oriented links. The retained global
source premise yields H_{D_ε} = H_{D_T}"), stated on the accepted vocabulary: along a jointly smooth
family `H` of oriented spatial embeddings (a smooth isotopy of the parametrized links, orientations
and component labels carried by the parameter) whose two ends have ordinary regular generic
projections, the HOMFLY–PT values `homfly` of any polygonal readings of the two end diagrams agree.
This is lit:homfly's fifth clause "Its value depends only on the oriented link presented by D" read
SPATIALLY.  The frozen `SM.lit_homfly` reads it as `HomflyClauses.descent` over `LinkEquiv` (planar
isotopy + the three moves); deriving this clause from that one is Reidemeister's theorem for smooth
isotopies of the polygonal readings (`AmbientIsotopyLinkEquiv` below), excluded by design D2, and no
other accepted declaration relates a `Diagram` to a point of `ℝ³`.  A `def … : Prop`, not itself an axiom:
the row is proved conditionally on it (`cp_finite_contact_path_of_descent`).  THE ASSUMPTION LIVES in
SM/LitHomflyDescent.lean as the registered literature axiom `SM.lit_homfly_descent : AmbientIsotopyDescent`
(policy label "lit:homfly (descent sentence)": the second declaration of lit:homfly authorised by the
author's decision D-GAP2 of 2026-09-15; interface review work/reviews/lit-homfly-descent.json), and row 91 is
`SM.cp_finite_contact_path := cp_finite_contact_path_of_descent lit_homfly_descent` (SM/ContactPath.lean).
Fidelity: the clause
bundles the isotopy-extension step the printed proof performs by hand (3276-3312) with the literature
premise; the split is `IsotopyExtension ∧ AmbientIsotopyDescentLit` (§1.2). -/
def AmbientIsotopyDescent : Prop :=
  ∀ {c : ℕ} (H : SpatialFamily c),
    (H.G 0).RegularGenericProjection → (H.G 1).RegularGenericProjection →
    ∀ X₀ X₁ : Diagram,
      Nonempty ((H.G 0).HeightMarking (H.G 0).projLoop X₀) →
      Nonempty ((H.G 1).HeightMarking (H.G 1).projLoop X₁) →
      homfly X₀ = homfly X₁

/-- The memo's form of the gap (GAP2_STATEMENTS_MEMO.md §1, §6): the polygonal readings of the two
ends of a smooth spatial family with regular generic projections are `LinkEquiv` — Reidemeister's
theorem for smooth isotopies of spatial links (with the PL reading of the ends).  Stronger than
`AmbientIsotopyDescent` (`AmbientIsotopyLinkEquiv.descent`); what closing GAP-2 by route (β) of the
memo would prove. -/
def AmbientIsotopyLinkEquiv : Prop :=
  ∀ {c : ℕ} (H : SpatialFamily c),
    (H.G 0).RegularGenericProjection → (H.G 1).RegularGenericProjection →
    ∀ X₀ X₁ : Diagram,
      Nonempty ((H.G 0).HeightMarking (H.G 0).projLoop X₀) →
      Nonempty ((H.G 1).HeightMarking (H.G 1).projLoop X₁) →
      LinkEquiv X₀ X₁

/-- Reidemeister + the frozen descent clause give the spatial descent clause. -/
theorem AmbientIsotopyLinkEquiv.descent (h : AmbientIsotopyLinkEquiv) : AmbientIsotopyDescent :=
  fun H h0 h1 X₀ X₁ m₀ m₁ => homfly_descent (h H h0 h1 X₀ X₁ m₀ m₁)

/-! ### 1.2 The printed proof's own split: isotopy extension + the literature premise -/

/-- "an actual ambient isotopy between the two oriented links" (sm-3:3310-3311), as the printed proof
produces it (3276-3312): a jointly smooth family of diffeomorphisms `Φ_s` of `ℝ³` (with smooth
inverses `Ψ_s`), `Φ_0 = id`, fixing the complement of a compact set (hence orientation-preserving),
whose end carries the parametrized `L₀` to the parametrized `L₁` (orientation and component labels
carried by the parameter). -/
structure AmbientIsotopy {c : ℕ} (L₀ L₁ : SpatialLink c) where
  Φ : ℝ → Space → Space
  Ψ : ℝ → Space → Space
  smooth : ContDiff ℝ ∞ (fun p : ℝ × Space => Φ p.1 p.2)
  smooth_inv : ContDiff ℝ ∞ (fun p : ℝ × Space => Ψ p.1 p.2)
  left_inv : ∀ s x, Ψ s (Φ s x) = x
  right_inv : ∀ s x, Φ s (Ψ s x) = x
  start : ∀ x, Φ 0 x = x
  compact_support : ∃ K : Set Space, IsCompact K ∧ ∀ s x, x ∉ K → Φ s x = x
  carries : ∀ (i : Fin c) (t : ℝ), Φ 1 (L₀.T i t) = L₁.T i t

/-- lit:homfly's fifth clause, literally, on spatial links: ambient-isotopic oriented links with
regular generic projections have the same `homfly` on any polygonal readings.  What the printed proof
cites ("The retained global source premise", 3311-3312); out of scope by D2 exactly as
`AmbientIsotopyDescent`. -/
def AmbientIsotopyDescentLit : Prop :=
  ∀ {c : ℕ} (L₀ L₁ : SpatialLink c), Nonempty (AmbientIsotopy L₀ L₁) →
    L₀.RegularGenericProjection → L₁.RegularGenericProjection →
    ∀ X₀ X₁ : Diagram,
      Nonempty (L₀.HeightMarking L₀.projLoop X₀) → Nonempty (L₁.HeightMarking L₁.projLoop X₁) →
      homfly X₀ = homfly X₁

/-- The isotopy extension step the printed proof performs by hand (sm-3:3276-3312: normal charts,
uniform normal radius, compactly supported velocity field, ODE flow): a smooth family of embeddings
of the finite union of circles is carried by an ambient isotopy.  TRUE (the isotopy extension theorem
for compact submanifolds); pure analysis, NOT excluded by any policy, outside the horizon by effort. -/
def IsotopyExtension : Prop :=
  ∀ {c : ℕ} (H : SpatialFamily c), Nonempty (AmbientIsotopy (H.G 0) (H.G 1))

/-- the printed split reassembled: isotopy extension + the literal premise give the clause consumed -/
theorem ambientIsotopyDescent_of_lit (hlit : AmbientIsotopyDescentLit) (hext : IsotopyExtension) :
    AmbientIsotopyDescent :=
  fun H h0 h1 X₀ X₁ m₀ m₁ => hlit (H.G 0) (H.G 1) (hext H) h0 h1 X₀ X₁ m₀ m₁

/-! ### 1.3 Consequences of the descent clause used by the proof (Unit A) -/

namespace AmbientIsotopyDescent

/-- (A-1) "Theorem lp:core identifies these original values with P on both actual diagrams"
(sm-3:3313-3314): the descent clause for `P` via `P_eq_homfly`. -/
theorem P_eq (hdesc : AmbientIsotopyDescent) {c : ℕ} (H : SpatialFamily c)
    (h0 : (H.G 0).RegularGenericProjection) (h1 : (H.G 1).RegularGenericProjection)
    {X₀ X₁ : Diagram} (m₀ : Nonempty ((H.G 0).HeightMarking (H.G 0).projLoop X₀))
    (m₁ : Nonempty ((H.G 1).HeightMarking (H.G 1).projLoop X₁)) : P X₀ = P X₁ := by
  rw [P_eq_homfly, P_eq_homfly]
  exact hdesc H h0 h1 X₀ X₁ m₀ m₁

/-- (A-2) the same with the two ends named by equations (so that a family whose ends are only
propositionally `L₀`, `L₁` can be used without rewriting inside dependent types) -/
theorem P_eq_of_ends (hdesc : AmbientIsotopyDescent) {c : ℕ} (H : SpatialFamily c)
    {L₀ L₁ : SpatialLink c} (e₀ : H.G 0 = L₀) (e₁ : H.G 1 = L₁)
    (h0 : L₀.RegularGenericProjection) (h1 : L₁.RegularGenericProjection)
    {X₀ X₁ : Diagram} (m₀ : Nonempty (L₀.HeightMarking L₀.projLoop X₀))
    (m₁ : Nonempty (L₁.HeightMarking L₁.projLoop X₁)) : P X₀ = P X₁ := by
  subst e₀
  subst e₁
  exact hdesc.P_eq H h0 h1 m₀ m₁

end AmbientIsotopyDescent

/-! ## 2. Unit B — the concatenated family `H_s` (sm-3:3259-3268)

"Let η : [0,1] → [0,1] be smooth and increasing, with its endpoint values 0, 1 and every
positive-order derivative zero at both endpoints. … Put H_s = L_{1−η(2s)} (0 ≤ s ≤ 1/2),
G_{η(2s−1)} (1/2 ≤ s ≤ 1). Both branches equal L at the join. Every positive-order time derivative
vanishes there; mixed parameter derivatives have the same property, while pure circle derivatives
agree with those of L. Thus the chain rule gives joint smoothness, including at the join. Every slice
is one of the supplied or proved embeddings. The literal endpoints are L_1, T."

`η := Real.smoothTransition` (Mathlib: `C^∞`, `0` on `(−∞, 0]`, `1` on `[1, ∞)`, values in `[0, 1]`).
Each half is a reparametrisation of a `SpatialFamily` by a smooth clock, hence jointly smooth on all
of `ℝ × ℝ`; the first half is the constant `L` on `[1/2, ∞)`, the second on `(−∞, 1/2]`; the glued
family equals `A + B − L` pointwise, which makes joint smoothness at the join a sum of smooth maps. -/

namespace SpatialFamily

variable {c : ℕ}

/-- (B-1) reparametrisation of a family by a smooth clock `φ` -/
def reparam (F : SpatialFamily c) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) : SpatialFamily c where
  G s := F.G (φ s)
  joint_smooth i :=
    (F.joint_smooth i).comp ((hφ.comp contDiff_fst).prodMk contDiff_snd)

@[simp] theorem reparam_G (F : SpatialFamily c) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (s : ℝ) :
    (F.reparam φ hφ).G s = F.G (φ s) := rfl

/-- (B-2) the glued family of two families that are the constant `L` on the two closed sides of the
join `s = 1/2`; joint smoothness is the leaf `glue_joint_smooth` -/
theorem glue_joint_smooth (A B : SpatialFamily c) (L : SpatialLink c)
    (hA : ∀ s : ℝ, 1 / 2 ≤ s → A.G s = L) (hB : ∀ s : ℝ, s ≤ 1 / 2 → B.G s = L) (i : Fin c) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (if p.1 ≤ 1 / 2 then A.G p.1 else B.G p.1).T i p.2) := by
  have key : (fun p : ℝ × ℝ => (if p.1 ≤ 1 / 2 then A.G p.1 else B.G p.1).T i p.2) =
      fun p : ℝ × ℝ => (A.G p.1).T i p.2 + (B.G p.1).T i p.2 - L.T i p.2 := by
    funext p
    split_ifs with h
    · rw [hB p.1 h]
      abel
    · rw [hA p.1 (le_of_lt (not_le.mp h))]
      abel
  rw [key]
  exact ((A.joint_smooth i).add (B.joint_smooth i)).sub ((L.smooth i).comp contDiff_snd)

/-- (B-3) the glued family: `A` up to the join, `B` after it -/
def glue (A B : SpatialFamily c) (L : SpatialLink c)
    (hA : ∀ s : ℝ, 1 / 2 ≤ s → A.G s = L) (hB : ∀ s : ℝ, s ≤ 1 / 2 → B.G s = L) :
    SpatialFamily c where
  G s := if s ≤ 1 / 2 then A.G s else B.G s
  joint_smooth i := glue_joint_smooth A B L hA hB i

theorem glue_G_of_le (A B : SpatialFamily c) (L : SpatialLink c)
    (hA : ∀ s : ℝ, 1 / 2 ≤ s → A.G s = L) (hB : ∀ s : ℝ, s ≤ 1 / 2 → B.G s = L)
    {s : ℝ} (hs : s ≤ 1 / 2) : (glue A B L hA hB).G s = A.G s := by
  show (if s ≤ 1 / 2 then A.G s else B.G s) = A.G s
  simp only [hs, ↓reduceIte]

theorem glue_G_of_lt (A B : SpatialFamily c) (L : SpatialLink c)
    (hA : ∀ s : ℝ, 1 / 2 ≤ s → A.G s = L) (hB : ∀ s : ℝ, s ≤ 1 / 2 → B.G s = L)
    {s : ℝ} (hs : 1 / 2 < s) : (glue A B L hA hB).G s = B.G s := by
  show (if s ≤ 1 / 2 then A.G s else B.G s) = B.G s
  simp only [not_le.mpr hs, ↓reduceIte]

/-- (B-4) "Both branches equal L at the join" -/
theorem glue_G_half (A B : SpatialFamily c) (L : SpatialLink c)
    (hA : ∀ s : ℝ, 1 / 2 ≤ s → A.G s = L) (hB : ∀ s : ℝ, s ≤ 1 / 2 → B.G s = L) :
    (glue A B L hA hB).G (1 / 2) = L ∧ A.G (1 / 2) = L ∧ B.G (1 / 2) = L := by
  refine ⟨?_, hA _ le_rfl, hB _ le_rfl⟩
  rw [glue_G_of_le A B L hA hB le_rfl]
  exact hA _ le_rfl

end SpatialFamily

/-! ### 2.2 The two clocks -/

/-- the clock of the first half, `s ↦ 1 − η(2s)`, the printed `η` being `Real.smoothTransition` -/
def roundClock (s : ℝ) : ℝ := 1 - Real.smoothTransition (2 * s)

/-- the clock of the second half, `s ↦ η(2s − 1)` -/
def pathClock (s : ℝ) : ℝ := Real.smoothTransition (2 * s - 1)

/-- (B-5) -/
theorem roundClock_contDiff : ContDiff ℝ ∞ roundClock := by
  unfold roundClock
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id))

/-- (B-6) -/
theorem pathClock_contDiff : ContDiff ℝ ∞ pathClock := by
  unfold pathClock
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- (B-7) the first clock has run out at and after the join -/
theorem roundClock_of_half_le {s : ℝ} (hs : 1 / 2 ≤ s) : roundClock s = 0 := by
  unfold roundClock
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/-- (B-8) the first clock starts at the end `L_1` of the rounding family -/
theorem roundClock_zero : roundClock 0 = 1 := by
  unfold roundClock
  rw [mul_zero, Real.smoothTransition.zero]
  ring

/-- (B-9) the second clock has not started at and before the join -/
theorem pathClock_of_le_half {s : ℝ} (hs : s ≤ 1 / 2) : pathClock s = 0 := by
  unfold pathClock
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- (B-10) the second clock ends at `T` -/
theorem pathClock_one : pathClock 1 = 1 := by
  unfold pathClock
  norm_num

/-- (B-11) the clocks stay in `[0, 1]` ("every slice is one of the supplied or proved embeddings") -/
theorem roundClock_mem (s : ℝ) : 0 ≤ roundClock s ∧ roundClock s ≤ 1 := by
  unfold roundClock
  constructor
  · linarith [Real.smoothTransition.le_one (2 * s)]
  · linarith [Real.smoothTransition.nonneg (2 * s)]

theorem pathClock_mem (s : ℝ) : 0 ≤ pathClock s ∧ pathClock s ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-! ### 2.3 The concatenation `H_s` for a rounding family `R` of `L` and a supplied family `F` -/

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

/-- the first half `s ↦ L_{1 − η(2s)}` -/
def roundHalf : SpatialFamily c := R.fam.reparam roundClock roundClock_contDiff

/-- (B-12) the first half is the constant `L` from the join on -/
theorem roundHalf_G_of_half_le {s : ℝ} (hs : 1 / 2 ≤ s) : R.roundHalf.G s = L := by
  show R.fam.G (roundClock s) = L
  rw [roundClock_of_half_le hs, R.start]

theorem roundHalf_G_zero : R.roundHalf.G 0 = R.fam.G 1 := by
  show R.fam.G (roundClock 0) = R.fam.G 1
  rw [roundClock_zero]

/-- the second half `s ↦ G_{η(2s − 1)}` -/
def pathHalf (F : SpatialFamily c) : SpatialFamily c := F.reparam pathClock pathClock_contDiff

/-- (B-13) the second half is the constant `L` up to the join -/
theorem pathHalf_G_of_le_half (F : SpatialFamily c) (hF0 : F.G 0 = L) {s : ℝ} (hs : s ≤ 1 / 2) :
    (pathHalf F).G s = L := by
  show F.G (pathClock s) = L
  rw [pathClock_of_le_half hs, hF0]

theorem pathHalf_G_one (F : SpatialFamily c) : (pathHalf F).G 1 = F.G 1 := by
  show F.G (pathClock 1) = F.G 1
  rw [pathClock_one]

/-- **The flattened family `H_s`** (cp:flattened-family, sm-3:3263-3268): the rounding family run
backwards from `L_1` to `L`, then the supplied family from `L` to `T`. -/
def contactPath (F : SpatialFamily c) (hF0 : F.G 0 = L) : SpatialFamily c :=
  SpatialFamily.glue R.roundHalf (pathHalf F) L (fun _ hs => R.roundHalf_G_of_half_le hs)
    (fun _ hs => pathHalf_G_of_le_half F hF0 hs)

/-- (B-14) "The literal endpoints are L_1, T": the start -/
theorem contactPath_G_zero (F : SpatialFamily c) (hF0 : F.G 0 = L) :
    (R.contactPath F hF0).G 0 = R.fam.G 1 := by
  unfold contactPath
  rw [SpatialFamily.glue_G_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact R.roundHalf_G_zero

/-- (B-15) … and the end -/
theorem contactPath_G_one (F : SpatialFamily c) (hF0 : F.G 0 = L) :
    (R.contactPath F hF0).G 1 = F.G 1 := by
  unfold contactPath
  rw [SpatialFamily.glue_G_of_lt _ _ _ _ _ (by norm_num : (1 / 2 : ℝ) < 1)]
  exact pathHalf_G_one F

/-- (B-16) "Both branches equal L at the join." -/
theorem contactPath_G_half (F : SpatialFamily c) (hF0 : F.G 0 = L) :
    (R.contactPath F hF0).G (1 / 2) = L :=
  (SpatialFamily.glue_G_half _ _ _ _ _).1

/-- (B-17) "Every slice is one of the supplied or proved embeddings." -/
theorem contactPath_slice (F : SpatialFamily c) (hF0 : F.G 0 = L) (s : ℝ) :
    (∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ (R.contactPath F hF0).G s = R.fam.G lam) ∨
    (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (R.contactPath F hF0).G s = F.G t) := by
  by_cases hs : s ≤ 1 / 2
  · left
    refine ⟨roundClock s, (roundClock_mem s).1, (roundClock_mem s).2, ?_⟩
    unfold contactPath
    rw [SpatialFamily.glue_G_of_le _ _ _ _ _ hs]
    rfl
  · right
    refine ⟨pathClock s, (pathClock_mem s).1, (pathClock_mem s).2, ?_⟩
    unfold contactPath
    rw [SpatialFamily.glue_G_of_lt _ _ _ _ _ (not_le.mp hs)]
    rfl

/-- (B-18) the start has an ordinary finite regular generic diagram (`D_ε`, sm-3:3238-3239) -/
theorem contactPath_start_generic (F : SpatialFamily c) (hF0 : F.G 0 = L) :
    ((R.contactPath F hF0).G 0).RegularGenericProjection := by
  rw [R.contactPath_G_zero]
  exact R.generic 1 zero_lt_one le_rfl

/-- (B-19) the end has one (`D_T`, the hypothesis) -/
theorem contactPath_end_generic (F : SpatialFamily c) (hF0 : F.G 0 = L)
    (hT : (F.G 1).RegularGenericProjection) :
    ((R.contactPath F hF0).G 1).RegularGenericProjection := by
  rw [R.contactPath_G_one]
  exact hT

end CuspRoundingFamily

/-! ## 3. Unit C — the polygonal reading of `D_ε = p(L_1)` from a reading of `S(F)`
(sm-3:3247-3250: "The two actual diagrams S(F) and D_ε have identical named decorated records. Each
clean cusp replacement inserts no crossing visit and keeps the same oriented attachments. All crossing
pairings, cyclic successors, signs, O/U bits and crossing-free component circles agree.")

The accepted `HeightMarking.ofSmoothing` reads a marking of a clean smoothing `G` as a marking of the
projection; its inverse `toSmoothing` reads a marking of the projection as a marking of ANY clean
smoothing — in particular of `p(L_1)`.  So the polygonal diagram `S` carrying `S(F)` also carries
`D_ε`; no existence of polygonal carriers is asserted (FR-1). -/

namespace SpatialLink

namespace HeightMarking

variable {c : ℕ} {L : SpatialLink c} {G : Fin c → SmoothLoop} {S : Diagram}

/-- (C-1) **Transport from the projection to a clean cusp smoothing** (the inverse of the accepted
`ofSmoothing`): the occurrences are the same parameters (`occEquiv`), meeting is transported by
`eval_eq_iff`, the over rule is `L`'s heights on both sides, the signs by `crossSignOf_eq`. -/
def toSmoothing (hfin : L.cuspSet.Finite) (r : L.CleanCuspSmoothing G)
    (m : L.HeightMarking L.projLoop S) : L.HeightMarking G S where
  e := m.e
  Φ := r.occEquiv.trans m.Φ
  comp_eq p := m.comp_eq (r.occEquiv p)
  between_iff p q s hpq hqs :=
    m.between_iff (r.occEquiv p) (r.occEquiv q) (r.occEquiv s) hpq hqs
  pair_eq p q hne he :=
    m.pair_eq (r.occEquiv p) (r.occEquiv q) (fun h => hne (r.occEquiv.injective h))
      ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mp he)
  over_iff p q hne he :=
    m.over_iff (r.occEquiv p) (r.occEquiv q) (fun h => hne (r.occEquiv.injective h))
      ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mp he)
  sgn_eq p q hne he hs := by
    have hd : IsDoubleOf L.projLoop p.1 q.1 :=
      (r.isDoubleOf_iff p.1 q.1).mp (OccOf.isDoubleOf_of_ne hne he)
    have h := m.sgn_eq (r.occEquiv p) (r.occEquiv q) (fun h => hne (r.occEquiv.injective h))
      ((r.eval_eq_iff (OccOf.not_sameParam_of_ne hne)).mp he) hs
    rw [r.crossSignOf_eq hfin hd]
    exact h

/-- (C-2) the inverse of the accepted `ofHeightOrder`: a reading with `L`'s heights is a reading with
the heights of any `L₁` ordering the branches of every double point of `G` as `L` does -/
def toHeightOrder {L₁ : SpatialLink c}
    (hh : ∀ p q : Param c, IsDoubleOf G p q → (L₁.height p < L₁.height q ↔ L.height p < L.height q))
    (m : L.HeightMarking G S) : L₁.HeightMarking G S :=
  ofHeightOrder (L := L₁) (L₁ := L) (fun p q hd => (hh p q hd).symm) m

end HeightMarking

end SpatialLink

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

/-- (C-3) the reading of `D_ε = p(L_1)` (with `L_1`'s own heights) carried by the polygonal diagram
`S` of a clean smoothing `S(F)` (with `L`'s heights): `S(F) → p(L) → p(L_1)`, then the height order
of `L_1` at the retained crossings is `L`'s (`same_data`) -/
def readingOfSmoothing (hL : L.CuspedProjection) {G : Fin c → SmoothLoop} {S : Diagram}
    (r : L.CleanCuspSmoothing G) (m : L.HeightMarking G S) :
    (R.fam.G 1).HeightMarking (R.fam.G 1).projLoop S :=
  SpatialLink.HeightMarking.toHeightOrder
    (fun p q hd => R.height_lt_iff_end ((R.same_doubles_end p q).mp hd))
    ((m.ofSmoothing hL.cusps_finite r).toSmoothing hL.cusps_finite R.endSmoothing)

/-- (C-4) hence `D_ε` has a polygonal reading as soon as `S(F)` has one -/
theorem exists_endpoint_reading (hL : L.CuspedProjection) {G : Fin c → SmoothLoop} {S : Diagram}
    (hG : Nonempty (L.CleanCuspSmoothing G)) (hS : Nonempty (L.HeightMarking G S)) :
    ∃ Xε : Diagram, Nonempty ((R.fam.G 1).HeightMarking (R.fam.G 1).projLoop Xε) :=
  hG.elim fun r => hS.elim fun m => ⟨S, ⟨R.readingOfSmoothing hL r m⟩⟩

end CuspRoundingFamily

/-! ## 4. Unit D — the two polynomial equalities of the printed proof -/

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

/-- (D-1) display cp:smoothing-record (sm-3:3251-3255): "Corollary ce:smoothing-record (through Lemma
rp:record-polynomial) therefore gives P_{S(F)} = P_{D_ε}" — the accepted row 90 -/
theorem P_eq_endpoint_reading (hL : L.CuspedProjection) (hc : 0 < c) {Xε : Diagram}
    (hXε : Nonempty ((R.fam.G 1).HeightMarking (R.fam.G 1).projLoop Xε))
    {G : Fin c → SmoothLoop} {S : Diagram}
    (hG : Nonempty (L.CleanCuspSmoothing G)) (hS : Nonempty (L.HeightMarking G S)) :
    P S = P Xε :=
  (ce_smoothing_record.source_and_polynomial L hc hL R Xε hXε G S hG hS).2

/-- (D-2) "The retained global source premise yields H_{D_ε} = H_{D_T}. Theorem lp:core identifies
these original values with P on both actual diagrams, proving P_{D_ε} = P_{D_T}" (sm-3:3311-3314):
the descent clause on the flattened family `H_s` -/
theorem P_endpoint_eq_of_descent (hdesc : AmbientIsotopyDescent) (F : SpatialFamily c)
    (hF0 : F.G 0 = L) (hT : (F.G 1).RegularGenericProjection) {Xε X : Diagram}
    (hXε : Nonempty ((R.fam.G 1).HeightMarking (R.fam.G 1).projLoop Xε))
    (hX : Nonempty ((F.G 1).HeightMarking (F.G 1).projLoop X)) : P Xε = P X :=
  hdesc.P_eq_of_ends (R.contactPath F hF0) (R.contactPath_G_zero F hF0) (R.contactPath_G_one F hF0)
    (R.generic 1 zero_lt_one le_rfl) hT hXε hX

end CuspRoundingFamily

/-! ## 5. Unit E — the row -/

/-- (E-1) "Use Lemma ce:rounding on the exact germs" (sm-3:3235): the accepted row 89 -/
theorem exists_cuspRoundingFamily' {c : ℕ} (L : SpatialLink c) (hc : 0 < c)
    (hL : L.CuspedProjection) : Nonempty (CuspRoundingFamily L) :=
  ce_rounding.exists_cuspRoundingFamily L hc hL

/-- (E-2) display cp:endpoint-polynomial from the descent clause: "Combining this equality with
cp:smoothing-record proves cp:endpoint-polynomial" (sm-3:3314-3315) -/
theorem endpoint_polynomial_of_descent (hdesc : AmbientIsotopyDescent) {c : ℕ} (L : SpatialLink c)
    (hc : 0 < c) (hL : L.CuspedProjection) (F : SpatialFamily c) (hF0 : F.G 0 = L)
    (hT : (F.G 1).RegularGenericProjection) (X : Diagram)
    (hX : Nonempty ((F.G 1).HeightMarking (F.G 1).projLoop X)) (G : Fin c → SmoothLoop)
    (S : Diagram) (hG : Nonempty (L.CleanCuspSmoothing G)) (hS : Nonempty (L.HeightMarking G S)) :
    P S = P X := by
  obtain ⟨R⟩ := exists_cuspRoundingFamily' L hc hL
  obtain ⟨Xε, hXε⟩ := R.exists_endpoint_reading hL hG hS
  calc P S = P Xε := R.P_eq_endpoint_reading hL hc hXε hG hS
    _ = P X := R.P_endpoint_eq_of_descent hdesc F hF0 hT hXε hX

/-! ### 5.2 The hypothesis fields read back on the vocabulary (E-3 … E-7) -/

/-- (E-3) sm-3:3212-3214 -/
theorem link_class_reading {c : ℕ} (L : SpatialLink c) :
    (∀ i, ContDiff ℝ ∞ (L.T i)) ∧ (∀ i, Function.Periodic (L.T i) 1) ∧
    (∀ (i j : Fin c) (s t : ℝ), L.T i s = L.T j t → i = j ∧ SameT s t) ∧
    (∀ i t, deriv (L.T i) t ≠ 0) :=
  ⟨L.smooth, L.periodic, L.embedded, L.regular⟩

/-- (E-4) sm-3:3214-3219 -/
theorem cusped_front_reading {c : ℕ} (L : SpatialLink c) (hL : L.CuspedProjection) :
    L.cuspSet.Finite ∧ (∀ p ∈ L.cuspSet, L.ExactCuspGerm p.1 p.2) :=
  ⟨hL.cusps_finite, hL.exact_germ⟩

/-- (E-5) sm-3:3220-3222 ("none at a cusp" is CE-R3's theorem) -/
theorem double_points_reading {c : ℕ} (L : SpatialLink c) (hL : L.CuspedProjection) :
    (occSetOf L.projLoop).Finite ∧
    (∀ p q : Param c, IsDoubleOf L.projLoop p q →
      det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0) ∧
    (∀ p q r : Param c, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
      IsDoubleOf L.projLoop p r → False) ∧
    (∀ p q : Param c, IsDoubleOf L.projLoop p q → ¬ L.IsCusp p.1 p.2) ∧
    (∀ p q : Param c, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q) :=
  ⟨hL.doubles_finite, hL.transverse, hL.no_triple,
    fun _ _ hd => SpatialLink.CuspedProjection.not_isCusp_of_isDouble L hL hd, hL.heights_distinct⟩

/-- a cuspless projection: the regular end has an empty cusp set -/
theorem SpatialLink.RegularGenericProjection.cuspSet_eq_empty {c : ℕ} {L : SpatialLink c}
    (h : L.RegularGenericProjection) : L.cuspSet = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  exact h.regular p.1 p.2 hp.2

/-- (E-6) sm-3:3222-3225 -/
theorem supplied_family_reading {c : ℕ} (L : SpatialLink c) (F : SpatialFamily c) (hF0 : F.G 0 = L)
    (hT : (F.G 1).RegularGenericProjection) :
    (∀ i, ContDiff ℝ ∞ (fun p : ℝ × ℝ => (F.G p.1).T i p.2)) ∧
    (∀ (t : ℝ) (i j : Fin c) (s s' : ℝ), (F.G t).T i s = (F.G t).T j s' → i = j ∧ SameT s s') ∧
    (∀ (t : ℝ) (i : Fin c) (s : ℝ), deriv ((F.G t).T i) s ≠ 0) ∧
    (∀ (t : ℝ) (i : Fin c), Function.Periodic ((F.G t).T i) 1) ∧
    (∀ i, (F.G 0).T i = L.T i) ∧
    (F.G 1).cuspSet = ∅ ∧ (occSetOf (F.G 1).projLoop).Finite ∧
    (∀ p q : Param c, IsDoubleOf (F.G 1).projLoop p q →
      det (deriv (xzOf ((F.G 1).T p.1)) p.2) (deriv (xzOf ((F.G 1).T q.1)) q.2) ≠ 0) ∧
    (∀ p q r : Param c, IsDoubleOf (F.G 1).projLoop p q → IsDoubleOf (F.G 1).projLoop q r →
      IsDoubleOf (F.G 1).projLoop p r → False) ∧
    (∀ p q : Param c, IsDoubleOf (F.G 1).projLoop p q → (F.G 1).height p ≠ (F.G 1).height q) :=
  ⟨F.joint_smooth, fun t => (F.G t).embedded, fun t => (F.G t).regular, fun t => (F.G t).periodic,
    fun i => by rw [hF0], hT.cuspSet_eq_empty, hT.doubles_finite, hT.transverse, hT.no_triple,
    hT.heights_distinct⟩

/-- (E-7) sm-3:3225-3227 -/
theorem smaller_y_over_reading {c : ℕ} (L : SpatialLink c) (G : Fin c → SmoothLoop) (S : Diagram)
    (r : L.CleanCuspSmoothing G) (m : L.HeightMarking G S) :
    (∀ p q : Param c, IsDoubleOf G p q ↔ IsDoubleOf L.projLoop p q) ∧
    (∀ k : L.cuspSet, ∀ t ∈ Set.Ioo (r.a k) (r.b k), ∀ q : Param c, ¬ SameParam (k.1.1, t) q →
      (G q.1).γ q.2 ≠ (G k.1.1).γ t) ∧
    ∀ p q : OccOf G, p ≠ q → (G p.1.1).γ p.1.2 = (G q.1.1).γ q.1.2 →
      (S.overBit (m.Φ p) = true ↔ L.height p.1 < L.height q.1) :=
  ⟨r.isDoubleOf_iff, r.no_crossing, m.over_iff⟩

/-! ### 5.3 The row, modulo the descent clause -/

/-- **Row 91 cp:finite-contact-path modulo GAP-2.**  Under the descent clause `AmbientIsotopyDescent`
(lit:homfly's fifth clause read spatially — the one step of the printed proof outside the frozen
interfaces), the row follows from the accepted rows 89 (`ce_rounding`) and 90 (`ce_smoothing_record`),
rp:record-polynomial (`presentations`) and lp:core (`P_eq_homfly`). -/
theorem cp_finite_contact_path_of_descent (hdesc : AmbientIsotopyDescent) : ContactPathData where
  link_class := fun L _ => link_class_reading L
  cusped_front := fun L _ hL => cusped_front_reading L hL
  double_points := fun L _ hL => double_points_reading L hL
  supplied_family := fun L F hF0 hT => supplied_family_reading L F hF0 hT
  smaller_y_over := fun L _ _ G S r m => smaller_y_over_reading L G S r m
  endpoint_polynomial := fun L hc hL F hF0 hT X hX G S hG hS =>
    endpoint_polynomial_of_descent hdesc L hc hL F hF0 hT X hX G S hG hS

/-- the same from Reidemeister's theorem for smooth isotopies (the memo's form of the gap) -/
theorem cp_finite_contact_path_of_linkEquiv (h : AmbientIsotopyLinkEquiv) : ContactPathData :=
  cp_finite_contact_path_of_descent h.descent

/-- the same from the printed proof's own split: isotopy extension (analysis, sm-3:3276-3312) plus
the literal literature premise on ambient isotopies -/
theorem cp_finite_contact_path_of_lit (hlit : AmbientIsotopyDescentLit) (hext : IsotopyExtension) :
    ContactPathData :=
  cp_finite_contact_path_of_descent (ambientIsotopyDescent_of_lit hlit hext)

end

end SM
