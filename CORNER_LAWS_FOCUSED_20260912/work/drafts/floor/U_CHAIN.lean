import SM.Curl
import SM.TransverseFront
import SM.CeSmoothingRecord
import SM.CornerStateSum
import SM.LinkPositiveLift
import SM.UniformRotation

/-! # Rows 99 cf:thm-carrierfloor and 100 thm:floor — FIXED STATEMENTS (judge's FINAL), 2026-09-15

Source: reference/SM/sm-3-statesum.tex:4282-4339 (row 99 statement), 4340-4575 (proof),
4576-4585 (row 100 statement), 4586-4602 (proof).  Judge, 2026-09-15, from the candidates
work/drafts/floor/Sketch_A.lean (Architect A, fidelity-first: WINNER for the statements — one field
per printed clause, redundant printed hypotheses kept, knot-case (R), literal reversal alternative,
`f_D` as the `z⁰` row) and Sketch_B.lean (Architect B, feasibility: GRAFTED — `tangencySet` /
`CrossesPositively` vocabulary, `InSupportM 1` for the `z`-parity clause, `Diagram.switchAll` facts,
`MirrorSubstitutionData`, `rotPlane`/`downDir`, the explicit transverse-lift formulas, the
`Θ`-based decomposition of (B), the unit interfaces).  Decision record: work/drafts/floor/PLAN_FINAL.md.

JUDGE'S REPAIR (§1): both candidates copied the gap2 memo's `SmoothKnotDiagram.Carries` as the
row-94 interface.  The contact lane (work/drafts/contact/DESIGN_A.md §3, DESIGN_B.md §3, both
sketches) has DROPPED `Carries`: fd:contact reads the front `D_T` polygonally through the ACCEPTED
`SpatialLink.HeightMarking` of `K.spatial : SpatialLink 1` (rows 90/91's own reading; record-level,
no point coincidence), and states the bound with the real self-linking number `sl`.  The floor lane's
hypothesis is therefore the sl-free composite of the two printed displays on THAT reading,
`TransverseFrontBound`, and `transverseFrontBound_of_fdContactShape` (PROVED below) derives it from
the contact lane's two clauses whatever `sl` they fix.  The transverse-lift unit outputs a
`HeightMarking` (FR-FL-C8).

Check: `cd work/lean && lake env lean ../drafts/floor/Statements_FINAL.lean` — 0 errors; the only
`sorry`s are the proof-route leaves of §8 (unit statements, frozen) and the two row theorems'
conditional forms are PROVED from them.  Nothing here is to be ported without the statement review.

Accepted inputs (work/lean): SM/Rounding.lean (cf:lem-rounding: `RoundingWitness`, `Carried`,
`PolygonDiagram`, `CornerRounding.roundedWitness/clearance/Admissible/juncArc/juncLen/uDir/vDir`),
SM/Curl.lean (cf:lem-curl: `RecordCarried`, `CurlSite`, `CurlWitness`, `cf_lem_curl`),
SM/TransverseFront.lean (`TransverseKnot`, `front`, `SmoothKnotDiagram.writhe`),
SM/CeSmoothingRecord.lean (`SpatialLink`, `projLoop`, `HeightMarking`), SM/TurningNumber.lean +
SM/TurnLift.lean (`ClosedC1Curve.rot`, `rot_reverse`), SM/RotationNumber.lean + SM/RotationReversal.lean
(lem:rot), SM/UniformRotation.lean (lem:uniformrot), SM/LinkDiagram.lean + SM/LinkMoves.lean
(`Diagram.reverse`, `reverse_sign`, `reverse_writhe`, `withOver`, `ReverseCarries`, `IsSkeinTriple.reverse`),
SM/PolynomialBlock.lean (lp:core, rp:record-polynomial), SM/CoefficientTransport.lean,
SM/LinkLaurentRing.lean (`coeffAt`, `degAZ`, `mindegAZ`, `mindegZZ`, `InSupportM`, `unitPowers`),
SM/CornerStateSum.lean (def:C), SM/LinkPositiveLift.lean, SM/CarrierCornerPolygon.lean (lem:carriers). -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The row-94 interface (fd:contact), in the contact lane's vocabulary — JUDGE'S REPAIR

`TransverseKnot.spatial` and `TransverseKnot.Reads` are copied VERBATIM from
work/drafts/contact/Sketch_A.lean §4 (= Sketch_B.lean §0 `spatial`); when the contact lane's module
lands they are deleted here and the names resolve to the accepted ones.  Both contact designs state
fd:contact as `FdContactData` with fields `front_writhe : sl K = ↑K.front.writhe` and
`representative_bound : K.Reads X → sl K ≤ −↑(degAZ (P X)) − 1`; `FdContactShape sl` is exactly that
pair, and `TransverseFrontBound` is their sl-free composite, the ONLY thing clause (C) consumes
(sm-3:4525-4531: "By Theorem fd:contact, sl(K_T) = w(T) = −w − R … max deg_a P_{D̄} ≤ −sl(K_T) − 1"). -/

/-- The transverse knot `T` of def:transverse-front as a one-component `SpatialLink` (rows 89-91
vocabulary; the same `Space`, the same period `1`).  Verbatim the contact lane's definition. -/
def TransverseKnot.spatial (K : TransverseKnot) : SpatialLink 1 where
  T := fun _ => K.T
  smooth := fun _ => K.smooth
  periodic := fun _ => K.periodic
  embedded := fun i j s t h => ⟨Subsingleton.elim i j, K.embedded s t h⟩
  regular := fun _ t => K.deriv_T_ne_zero t

@[simp] theorem TransverseKnot.spatial_T (K : TransverseKnot) (i : Fin 1) : K.spatial.T i = K.T := rfl

/-- the projection of the spatial link is the curve of the front (`xzOf K.T`, definitionally) -/
theorem TransverseKnot.spatial_projLoop_γ (K : TransverseKnot) (i : Fin 1) :
    (K.spatial.projLoop i).γ = xzOf K.T := rfl

/-- FR-1 for the front of `T`: the polygonal `Diagram X` reads `D_T` with `T`'s own heights (over =
smaller `y`) — the accepted record-level `HeightMarking` (SM/CeSmoothingRecord.lean: occurrence
bijection, cyclic order, twin pairing, over = smaller height, signs; no point coincidence).  The
contact lane's `TransverseKnot.Reads`, verbatim. -/
def TransverseKnot.Reads (K : TransverseKnot) (X : Diagram) : Prop :=
  Nonempty (K.spatial.HeightMarking K.spatial.projLoop X)

/-- The writhe bound of row 94 fd:contact in its sl-free form, the EXPLICIT HYPOTHESIS of the (C)
route until row 94 lands: "for every transverse knot `K` and every polygonal reading `X` of its
front, `w(front) ≤ −max deg_a P_X − 1`" (the composite of fd:front-writhe and
fd:representative-bound). -/
def TransverseFrontBound : Prop :=
  ∀ (K : TransverseKnot) (X : Diagram), K.Reads X → K.front.writhe ≤ -degAZ (P X) - 1

/-- The two displays of fd:contact as the contact lane states them (`FdContactData.front_writhe`,
`FdContactData.representative_bound`, for the lane's real-valued `sl`); the first sentence
`over_rule_sign` (definitional on the class) is not needed here. -/
structure FdContactShape (sl : TransverseKnot → ℝ) : Prop where
  /-- display fd:front-writhe: `sl(T) = Σ_q sgn det_xz(u_O(q), u_U(q))` -/
  front_writhe : ∀ K : TransverseKnot, sl K = (K.front.writhe : ℝ)
  /-- display fd:representative-bound: `sl(T) ≤ −max deg_a P_T(a,z) − 1` -/
  representative_bound : ∀ (K : TransverseKnot) (X : Diagram), K.Reads X →
    sl K ≤ -((degAZ (P X) : ℤ) : ℝ) - 1

/-- the floor lane's hypothesis follows from the contact lane's two displays, for any `sl` -/
theorem transverseFrontBound_of_fdContactShape {sl : TransverseKnot → ℝ} (h : FdContactShape sl) :
    TransverseFrontBound := by
  intro K X hX
  have h1 := h.representative_bound K X hX
  rw [h.front_writhe K] at h1
  exact_mod_cast h1

/-! ## 2. Clause (R) (sm-3:4283-4290) -/

/-- Clause (R), one field per printed sentence.  "Here rot is as in Lemma lem:rot for polygons and
Definition cf:def-turning for the underlying plane curve of a smooth diagram" scopes the last
sentence, which therefore has a polygon field and a `C¹`-curve field. -/
structure CarrierFloorRData : Prop where
  /-- "Let D be an oriented knot diagram and −D the same diagram with every arrow reversed.
  Then P_{−D} = P_D" (the row states the knot case, FR-FL-R1; the library lemma is unconditional) -/
  P_reverse : ∀ X : Diagram, X.componentCount = 1 → P X.reverse = P X
  /-- "consequently an oriented knot and its reverse have the same polynomial": the knot presented
  by `X` (its `LinkEquiv` class, design D2) and its reverse (presented by `X'.reverse` for any
  diagram `X'` of the knot) -/
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X
  /-- "Moreover −D has the same crossing signs" -/
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  /-- "and the same writhe as D" -/
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  /-- "and the rotation of its underlying plane curve is the negative of that of D" — polygonal
  diagram: the underlying curve of `X` is the polygon `C`, that of `−X` the reversed polygon, and
  lem:rot's `rot` is negated -/
  rot_reverse_polygon : ∀ (X : Diagram) (C : PolyComp), X.Γ = Shadow.single C →
    X.reverse.Γ = Shadow.single C.reverse ∧ rotationNumber C.reverse.P = -rotationNumber C.P
  /-- — smooth diagram: cf:def-turning's `rot` of the reversed `C¹` curve is negated -/
  rot_reverse_curve : ∀ γ : ClosedC1Curve, γ.reverse.rot = -γ.rot

/-! ## 3. Clause (A) (sm-3:4291-4305): the rounding record -/

/-- (A) `Round(L, D, ε) = (L_ε, D_ε)`: the accepted named construction of cf:lem-rounding
(`CornerRounding.roundedWitness`), a FUNCTION of the data `(L, D, ε)` (and the admissibility proof,
irrelevant).  `L_ε = (Round …).Lε`, `D_ε = D` carried (`(Round …).carried`). -/
def Round (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    RoundingWitness C D ε :=
  CornerRounding.roundedWitness h

/-- "the junction inserted at the corner q_i is determined by ε, by the two incident unit directions
and by the transition profile": the junction template at the corner `q` with incoming unit direction
`u` and outgoing unit direction `v` — the accepted `juncArc` (whose profile is the fixed
`Real.smoothTransition`) started at `q − ε u`, with the argument of `u` and the principal angle from
`u` to `v`. -/
def junctionTemplate (q u v : Plane) (ε s : ℝ) : Plane :=
  CornerRounding.juncArc (q - ε • u) ε (planeComplex u).arg (principalAngle u v) s

/-- Clause (A), one field per printed sub-clause, read on `Round`. -/
structure CarrierFloorAData : Prop where
  /-- "returns one curve and one diagram at those data" — one record -/
  one_record : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h h' : CornerRounding.Admissible C D ε), Round C D ε h = Round C D ε h'
  /-- — the curve is the named construction -/
  one_curve : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    (Round C D ε h).Lε = CornerRounding.roundedLoop h
  /-- — the diagram is `D` itself, carried, with its data inherited -/
  one_diagram : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    Nonempty (Carried (Round C D ε h).Lε D.toDiagram) ∧
    (Round C D ε h).carried.smoothWrithe = D.toDiagram.writhe
  /-- "the junction inserted at the corner q_i is determined by ε, by the two incident unit
  directions and by the transition profile, which is fixed once and for all" (FR-FL-A1: stated
  parametrically, on `[a j, b j]` rescaled to `[0, 1]`) -/
  junction_determined : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ), j < C.k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
    (Round C D ε h).Lε.γ ((Round C D ε h).a j + s * ((Round C D ε h).b j - (Round C D ε h).a j)) =
      junctionTemplate (C.P j) (CornerRounding.uDir C j) (CornerRounding.vDir C j) ε s
  /-- "the arc length ℓ is then determined by the endpoint condition" -/
  length_determined : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ), j < C.k →
    (Round C D ε h).speed * ((Round C D ε h).b j - (Round C D ε h).a j) =
        CornerRounding.juncLen ε (principalTurn C.P j) ∧
    (Round C D ε h).Lε.γ ((Round C D ε h).b j) = C.P j + ε • CornerRounding.vDir C j
  /-- "and the rest of the curve is L itself" (cf:lem-rounding (a) on the record) -/
  rest_is_L : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    (∀ p : Plane, p ∉ (⋃ i, cornerDisc C ε i) →
      (p ∈ Set.range (Round C D ε h).Lε.γ ↔ p ∈ polygonImage C)) ∧
    ∀ j < C.k, ∀ t ∈ Set.Icc ((Round C D ε h).b j) ((Round C D ε h).a (j + 1)),
      (Round C D ε h).Lε.γ t = (Round C D ε h).Lε.γ ((Round C D ε h).b j) +
        ((Round C D ε h).speed * (t - (Round C D ε h).b j)) • SM.normalize (edge C.P j)

/-- B's image form of the locality clause is a corollary of `junction_determined` (two records with
equal corner, incident unit directions and `ε` have equal junction images); stated for the reviewer,
proved in unit U-A. -/
theorem CarrierFloorAData.junction_local (hA : CarrierFloorAData)
    (C C' : PolyComp) (D : PolygonDiagram C) (D' : PolygonDiagram C') (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (h' : CornerRounding.Admissible C' D' ε)
    (j j' : ℕ) (hj : j < C.k) (hj' : j' < C'.k)
    (hq : C.P j = C'.P j') (hu : CornerRounding.uDir C j = CornerRounding.uDir C' j')
    (hv : CornerRounding.vDir C j = CornerRounding.vDir C' j') :
    (Round C D ε h).Lε.γ '' Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) =
      (Round C' D' ε h').Lε.γ '' Set.Icc ((Round C' D' ε h').a j') ((Round C' D' ε h').b j') := by
  sorry

/-! ## 4. Clause (B) (sm-3:4306-4318): the tangency count -/

/-- "either all principal turns are positive, or exactly one is negative and all others are
positive" (for the polygon as oriented) -/
def AllPosOrOneNeg {m : ℕ} (Q : LabelledTuple m) : Prop :=
  (∀ i, 0 < principalTurn Q i) ∨
  (∃ i, principalTurn Q i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn Q j)

/-- "after reversing orientation if necessary, either …": the alternative holds for `L` or for its
reversal (accepted `reversal`; reversal negates every principal turn, `principalTurn_reversal`) -/
def UniformOrOneDissent (C : PolyComp) : Prop :=
  AllPosOrOneNeg C.P ∨ AllPosOrOneNeg (reversal C.P)

/-- the reversed polygon diagram (`−D` on `−L`): the accepted `Diagram.reverse` read back on the
single reversed polygon -/
def PolygonDiagram.reverse {C : PolyComp} (D : PolygonDiagram C) : PolygonDiagram C.reverse :=
  PolygonDiagram.ofDiagram D.toDiagram.reverse rfl

/-- the parameters of the fundamental period at which the unit tangent of the record equals `u`
("the points at which its unit tangent equals u", FR-FL-B2) -/
def tangencySet {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (u : Plane) :
    Set ℝ :=
  {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}

/-- "at each of them the tangent crosses that direction in the positive sense": the parameter lies in
an open junction `(a j, b j)` whose tangent-angle lift `θ j` (cf:lem-rounding (b)) has positive
derivative there (FR-FL-B3) -/
def CrossesPositively {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (t : ℝ) : Prop :=
  ∃ j, j < C.k ∧ t ∈ Set.Ioo (W.a j) (W.b j) ∧ 0 < deriv (W.θ j) t

/-- "has exactly R points at which its unit tangent equals u …; at each of them the tangent crosses
that direction in the positive sense": the tangency set is FINITE (explicit, `Set.ncard` of an
infinite set is `0`) of cardinality `R`, and every tangency crosses positively -/
def TangencyCount {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (u : Plane) (R : ℝ) : Prop :=
  (tangencySet W u).Finite ∧ ((tangencySet W u).ncard : ℝ) = R ∧
  ∀ t ∈ tangencySet W u, CrossesPositively W t

/-- "there are a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁) the rounded curve L_ε
of the record Round(L, D, ε) from clause (A) has exactly R points at which its unit tangent equals u
and exactly R at which it equals −u; at each of them the tangent crosses that direction in the
positive sense", `R = |rot(L)|`.  `ε₁ ≤ ε₀(L)` so that the record exists at every such `ε`
(the printed proof takes `ε₁ = ε₀(L)`, FR-FL-B4); the admissibility proof `h` exists under the row's
nonzero-turn hypothesis and is irrelevant (`one_record`). -/
def BClaim (C : PolyComp) (D : PolygonDiagram C) : Prop :=
  ∃ (u : Plane) (ε₁ : ℝ), euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ CornerRounding.clearance C ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ h : CornerRounding.Admissible C D ε,
      TangencyCount (Round C D ε h) u |rotationNumber C.P| ∧
      TangencyCount (Round C D ε h) (-u) |rotationNumber C.P|

/-- Clause (B).  "Let L be a closed polygon with nonzero edges and nonzero principal turns, finitely
many transverse double points, no triple points, no corner at a double point and no corner on a
non-incident edge, carrying a diagram D" = `C : PolyComp`, `D : PolygonDiagram C` (its `generic`
field is that list, FR-FL-B5) and `∀ i, principalTurn C.P i ≠ 0`.  The claim is made for the polygon
in the normalised orientation ("after reversing orientation if necessary … perform the allowed
normalization once", sm-3:4368-4370): for `L` itself when `L` is already uniform / one-dissent, for
`−L` (carrying `−D`) otherwise (FR-FL-B1). -/
structure CarrierFloorBData : Prop where
  tangencies : ∀ (C : PolyComp) (D : PolygonDiagram C), (∀ i, principalTurn C.P i ≠ 0) →
    UniformOrOneDissent C →
    (AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)

/-! ## 5. Clause (C) (sm-3:4319-4337): the floor -/

/-- The hypotheses of clause (C), one field per printed clause (sm-3:4320-4333), on the oriented
knot diagram `X` whose underlying plane curve is the polygon `L = C.P`.  The three redundant fields
(`turn_exists`, `turn_lt_pi`, `generic`) are printed ("stated here so that no generic parent polygon
is assumed") and kept (FR-FL-C1); they follow from `shadow` and `X.generic`
(`CarrierFloorCHyp.of_diagram`). -/
structure CarrierFloorCHyp (C : PolyComp) (X : Diagram) : Prop where
  /-- "Let D be an oriented knot diagram … whose underlying plane curve is a closed polygon L"
  (one component: `(Shadow.single C).c = 1`) -/
  shadow : X.Γ = Shadow.single C
  /-- "all of whose crossings are positive" -/
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  /-- "with all principal turns existing" -/
  turn_exists : Regular C.P
  /-- "nonzero" -/
  turn_ne : ∀ i, principalTurn C.P i ≠ 0
  /-- "and of magnitude below π" -/
  turn_lt_pi : ∀ i, |principalTurn C.P i| < Real.pi
  /-- "with finitely many double points, all transversal (`transverse`), with no triple points
  (`no_triple`), none of them a corner of L, and no corner of L lying on a non-incident edge
  (`tail_off`)" — the accepted genericity of the one-polygon shadow, field for field -/
  generic : (Shadow.single C).Generic
  /-- "Assume that, after reversing the orientation if necessary …, either every principal turn is
  positive, or exactly one is negative and every other is positive" -/
  alternative : UniformOrOneDissent C

/-- The redundant fields from the accepted diagram: `Regular` and the genericity list are
`X.generic` after `shadow`; `|ϑ| < π` is the range of the principal angle on a regular pair
(`principalAngle_bounds`). -/
theorem CarrierFloorCHyp.of_diagram (C : PolyComp) (X : Diagram) (shadow : X.Γ = Shadow.single C)
    (positive : ∀ x : X.Γ.Crossing, X.IsPositive x) (turn_ne : ∀ i, principalTurn C.P i ≠ 0)
    (alternative : UniformOrOneDissent C) : CarrierFloorCHyp C X where
  shadow := shadow
  positive := positive
  turn_exists := (shadow ▸ X.generic).regular ⟨0, Nat.one_pos⟩
  turn_ne := turn_ne
  turn_lt_pi := fun i =>
    abs_lt.mpr (principalAngle_bounds ((shadow ▸ X.generic).regular ⟨0, Nat.one_pos⟩ i))
  generic := shadow ▸ X.generic
  alternative := alternative

/-- `f_D(a) = [z⁰] P_D(a, z)`, read as the element of `R` carrying the `z⁰` row of `f` (so that
def:adeg's `mindeg_a` applies to it): the monomials `a^d z^0` of `f` (FR-FL-C3). -/
def zZeroPart (f : R) : R :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun e : ℤ × ℤ => e.2 = 0) f.coeff)

theorem coeffAt_zZeroPart_zero (f : R) (d : ℤ) : coeffAt d 0 (zZeroPart f) = coeffAt d 0 f := by
  simp [zZeroPart, coeffAt]

theorem coeffAt_zZeroPart_of_ne (f : R) (d k : ℤ) (hk : k ≠ 0) : coeffAt d k (zZeroPart f) = 0 := by
  simp [zZeroPart, coeffAt, hk]

/-- Clause (C): "Then mindeg_a P_D(a,z) ≥ 1 − w − R [cf:eq-floor], and the same bound holds for
f_D(a) = [z⁰]P_D(a,z) whenever f_D ≠ 0", `w = X.writhe`, `R = |rot(L)|` (real, FR-FL-C2). -/
structure CarrierFloorCData : Prop where
  /-- cf:eq-floor -/
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  /-- "and the same bound holds for f_D(a) = [z⁰]P_D(a,z) whenever f_D ≠ 0" -/
  floor_zZero : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X → zZeroPart (P X) ≠ 0 →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (zZeroPart (P X)) : ℝ)

/-- B's coefficient form, a corollary of `floor` by `mindegAZ_spec` (`P X ≠ 0`, `P_ne_zero`): every
present monomial `a^d z^k` of `P_D` has `d ≥ 1 − w − R` (covers the monomials of `f_D`); the form the
consumers cb:singleton / lem:corner-values may prefer.  Proved in unit U-C. -/
theorem CarrierFloorCData.floor_support (hC : CarrierFloorCData) (C : PolyComp) (X : Diagram)
    (h : CarrierFloorCHyp C X) (d k : ℤ) (hdk : coeffAt d k (P X) ≠ 0) :
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (d : ℝ) := by
  sorry

/-! ## 6. The row bundle (proposed name `SM.cf_thm_carrierfloor : CarrierFloorData`; no fixed name in
work/lean/axiom-policy.json `targets`) -/

/-- cf:thm-carrierfloor: the four printed clauses. -/
structure CarrierFloorData : Prop where
  clauseR : CarrierFloorRData
  clauseA : CarrierFloorAData
  clauseB : CarrierFloorBData
  clauseC : CarrierFloorCData

/-! ## 7. Row 100 thm:floor (sm-3:4576-4585) -/

section Floor

open Carrier

variable {n : ℕ} [NeZero n]

/-- "either all turns are left, or exactly one turn is right" on the corner polygon `Q` (turns =
def:chirotope's `turn ∈ {−1, 0, +1}`, left = `1`; FR-FL-F2: every corner of the corner polygon) -/
def AllLeftOrOneRight {m : ℕ} (Q : LabelledTuple m) : Prop :=
  (∀ j, turn Q j = 1) ∨ (∃ j₀, turn Q j₀ = -1 ∧ ∀ j, j ≠ j₀ → turn Q j = 1)

/-- "after possibly reversing its orientation either all turns are left, or exactly one turn is
right": for the corner polygon of the subpolygon `Q` (accepted `ccpCornerPolygon`) or its reversal
(accepted `reversal`; FR-FL-F1, literal reversal form) -/
def CarrierUniformOrOneDissent (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  AllLeftOrOneRight (ccpCornerPolygon hn hP S q) ∨
  AllLeftOrOneRight (reversal (ccpCornerPolygon hn hP S q))

/-- thm:floor: "Let Q be a subpolygon of a decomposition of a generic polygon, and suppose that
after possibly reversing its orientation either all turns are left, or exactly one turn is right.
Then mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q, H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0."
`H⁺_Q = cornerHomfly`, `m_Q = carrierCrossingCount`, `r_Q = carrierRotation`, `d_Q = cornerSlot`
(def:C, accepted; `cornerSlot_cast` is the printed equality `d_Q = 1 − m_Q − |r_Q|`);
`ℤ[a^{±1}, z²] = M_1` is the accepted `InSupportM 1` (lp:support). -/
structure FloorTheoremData : Prop where
  /-- "mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q" (in `ℤ` with `d_Q = cornerSlot`, and as printed with the
  real `r_Q`) -/
  a_floor : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧
    1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤
      (mindegAZ (cornerHomfly hn hP S q hS) : ℝ)
  /-- "H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0" (no hypothesis on the turns, FR-FL-F3) -/
  z_parity : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS)

end Floor

/-! ## 8. The proof route: frozen unit statements (leaves `sorry`; prefixes per PLAN_FINAL.md §4).
Every unit file is a byte-identical copy of this file plus proofs of its leaves and prefixed helpers;
an assembler merges (the curl-lane pattern). -/

/-! ### 8.1 Unit U-R: reversal (lp:coefficient-transport + `ReverseCarries` + `IsSkeinTriple.reverse`) -/

/-- `D ↦ P_{−D}` is an `RCompetitor` (accepted `reverseCarries_planarIsotopic/RI/RII/RIII`,
`IsSkeinTriple.reverse`, the crossing-free circle is carried); hence `P X.reverse = P X` for EVERY
link diagram (the printed proof argues "on all oriented link diagrams"; the row states the knot case). -/
theorem ur_P_reverse_all (X : Diagram) : P X.reverse = P X := by
  sorry

theorem cf_thm_carrierfloor_R : CarrierFloorRData where
  P_reverse := fun X _ => ur_P_reverse_all X
  knot_reverse := fun X X' _ h => by
    rw [ur_P_reverse_all, P_eq_homfly, P_eq_homfly]
    exact (homfly_descent h).symm
  sign_reverse := Diagram.reverse_sign
  writhe_reverse := Diagram.reverse_writhe
  rot_reverse_polygon := fun X C hX =>
    ⟨by show X.Γ.reverseShadow = _; rw [hX],
      rotationNumber_reversal ((hX ▸ X.generic).regular ⟨0, Nat.one_pos⟩)⟩
  rot_reverse_curve := ClosedC1Curve.rot_reverse

/-! ### 8.2 Unit U-A: the two non-definitional fields of (A) -/

/-- `curveMap_on_junction` (Rounding.lean:1668) + `dirOf_θu` (1207) + `G1_dirOf_arg` (1172) +
scale invariance of `principalAngle` (`Complex.arg_real_mul` on `cornerRotor`) + `2π`-periodicity of
`juncArc` in its `θu` argument -/
theorem ua_junction_determined (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ) (hj : j < C.k) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Round C D ε h).Lε.γ ((Round C D ε h).a j + s * ((Round C D ε h).b j - (Round C D ε h).a j)) =
      junctionTemplate (C.P j) (CornerRounding.uDir C j) (CornerRounding.vDir C j) ε s := by
  sorry

/-- `b_sub_a` (1277), `speed = Λ`, `ℓ = juncLen ε (turn C j)` (504), `curveMap_b` (1661) -/
theorem ua_length_determined (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ) (hj : j < C.k) :
    (Round C D ε h).speed * ((Round C D ε h).b j - (Round C D ε h).a j) =
        CornerRounding.juncLen ε (principalTurn C.P j) ∧
    (Round C D ε h).Lε.γ ((Round C D ε h).b j) = C.P j + ε • CornerRounding.vDir C j := by
  sorry

theorem cf_thm_carrierfloor_A : CarrierFloorAData where
  one_record := fun _ _ _ _ _ => rfl
  one_curve := fun _ _ _ _ => rfl
  one_diagram := fun _ D _ h => ⟨⟨(Round _ D _ h).carried⟩, (Round _ D _ h).same_writhe⟩
  junction_determined := fun C D ε h j hj s hs => ua_junction_determined C D ε h j hj s hs
  length_determined := fun C D ε h j hj => ua_length_determined C D ε h j hj
  rest_is_L := fun _ _ _ h => ⟨(Round _ _ _ h).outside, (Round _ _ _ h).straight⟩

/-! ### 8.3 Unit U-B: the tangency count.  Library form with the direction a parameter
(`ub_tangencyCount_of_admissible`, `ub_exists_admissibleDirection`), then the row (PROVED from them).
B's finer decomposition through the construction's GLOBAL angle `Θ` (Rounding.lean:516,
`normalize_deriv_curveMap` 1785, `Θ_on_junction` 1469, `Θ_on_straight` 1480, `θu_last` 1223,
`G2_θu_eq` 1281, `liftAt_strictMonoOn` 1742) is frozen as the sub-leaves `ub_globalLift`,
`ub_exists_direction`, `ub_levelCount`; U-B3 derives the two library leaves from them. -/

/-- the printed choice of `u` (sm-3:4372-4376): a unit direction, neither it nor its antipode an edge
direction, and neither in the closed swept arc of any negative turn -/
def AdmissibleDirection (C : PolyComp) (u : Plane) : Prop :=
  euclideanLength u = 1 ∧
  (∀ i : ZMod C.k, SM.normalize (edge C.P i) ≠ u ∧ SM.normalize (edge C.P i) ≠ -u) ∧
  ∀ j : ZMod C.k, principalTurn C.P j < 0 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
    CornerRounding.dirOf ((planeComplex (CornerRounding.uDir C j)).arg + s * principalTurn C.P j) ≠ u ∧
    CornerRounding.dirOf ((planeComplex (CornerRounding.uDir C j)).arg + s * principalTurn C.P j) ≠ -u

/-- (U-B1) the construction's global angle `Θ` lifts the unit tangent of the record and equals the
junction lifts on the junctions (`Round C D ε h` is `roundedWitness h` definitionally:
`Lε.γ = curveMap C ε`, `θ = liftAt`) -/
theorem ub_globalLift (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε)
    (t : ℝ) :
    (Round C D ε h).T t = CornerRounding.dirOf (CornerRounding.Θ C ε t) ∧
    (∀ j, j < C.k → t ∈ Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) →
      CornerRounding.Θ C ε t = (Round C D ε h).θ j t) := by
  sorry

/-- (U-B1) an argument `φ` with `θu j ≢ φ (mod π)` for all `j` and, for a negative junction, no level
`φ + nπ` in its closed swept arc `[θu j + ϑ_j, θu j]` (the complement of the forbidden set in a period
is an open interval of length `π − |ϑ₋| > 0` minus finitely many points, `turn_bounds` 1155) -/
theorem ub_exists_direction (C : PolyComp) (hturn : ∀ i, principalTurn C.P i ≠ 0)
    (hpos : AllPosOrOneNeg C.P) :
    ∃ φ : ℝ, (∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ φ + n * Real.pi) ∧
      ∀ j, j < C.k → CornerRounding.turn C j < 0 →
        ∀ n : ℤ, φ + n * Real.pi ∉
          Set.Icc (CornerRounding.θu C j + CornerRounding.turn C j) (CornerRounding.θu C j) := by
  sorry

/-- (U-B2) the levels `φ + 2πℤ` are met exactly `rot(L)` times, all in open positive junctions with
positive angular derivative: per positive junction `⌊x_{j+1}⌋ − ⌊x_j⌋` levels (`liftAt` strictly
monotone and continuous, `θ_unique`), none on straight parts or junction ends (`liftAt_a/b`), none in
the negative junction (`θ_range`); telescoped by `G2_θu_eq` to `⌊x_0 + rot⌋ − ⌊x_0⌋ = rot`
(`θu_last`, `rotationNumber_integer`, `Int.floor_add_intCast`) -/
theorem ub_levelCount (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε)
    (φ : ℝ) (hφ : ∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ φ + n * Real.pi)
    (harc : ∀ j, j < C.k → CornerRounding.turn C j < 0 →
      ∀ n : ℤ, φ + n * Real.pi ∉
        Set.Icc (CornerRounding.θu C j + CornerRounding.turn C j) (CornerRounding.θu C j))
    (hrot : 0 < rotationNumber C.P) :
    TangencyCount (Round C D ε h) (CornerRounding.dirOf φ) (rotationNumber C.P) := by
  sorry

/-- (U-B3, library leaf) for every admissible direction and every admissible `ε` (the printed proof,
with `ε₁ = ε₀(L)`): from `ub_globalLift`, `ub_levelCount` at `φ` and at `φ + π` (`dirOf (φ + π) = −dirOf φ`),
`rot ≥ 1` in both normalised cases (`uniform_rotation` via `principalTurn_sign`), `|rot| = rot`. -/
theorem ub_tangencyCount_of_admissible (C : PolyComp) (D : PolygonDiagram C)
    (hturn : ∀ i, principalTurn C.P i ≠ 0) (hpos : AllPosOrOneNeg C.P) (u : Plane)
    (hu : AdmissibleDirection C u) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    TangencyCount (Round C D ε h) u |rotationNumber C.P| ∧
    TangencyCount (Round C D ε h) (-u) |rotationNumber C.P| := by
  sorry

/-- (U-B3, library leaf) "Such u exists" (sm-3:4374-4376): `u := dirOf φ` from `ub_exists_direction`
(`dirOf (θu j) = uDir j`, 1207). -/
theorem ub_exists_admissibleDirection (C : PolyComp) (hreg : Regular C.P)
    (hturn : ∀ i, principalTurn C.P i ≠ 0) (hpos : AllPosOrOneNeg C.P) :
    ∃ u : Plane, AdmissibleDirection C u := by
  sorry

theorem ub_BClaim (C : PolyComp) (D : PolygonDiagram C) (hturn : ∀ i, principalTurn C.P i ≠ 0)
    (hpos : AllPosOrOneNeg C.P) : BClaim C D := by
  obtain ⟨u, hu⟩ := ub_exists_admissibleDirection C D.regular hturn hpos
  refine ⟨u, CornerRounding.clearance C, hu.1, CornerRounding.clearance_pos D.generic, le_rfl,
    fun ε _ _ h => ub_tangencyCount_of_admissible C D hturn hpos u hu ε h⟩

theorem cf_thm_carrierfloor_B : CarrierFloorBData where
  tangencies := fun C D hturn halt => by
    rcases halt with hpos | hpos
    · exact Or.inl ⟨hpos, ub_BClaim C D hturn hpos⟩
    · refine Or.inr ⟨hpos, ub_BClaim C.reverse D.reverse ?_ hpos⟩
      intro i
      show principalTurn (reversal C.P) i ≠ 0
      rw [principalTurn_reversal D.regular]
      exact neg_ne_zero.mpr (hturn _)

/-! ### 8.4 Units U-SW / U-ι / U-EQ: the printed `D̄` ("the diagram with every crossing switched",
sm-3:4431, 4533 — NOT the accepted reflection `Diagram.mirror`, FR-FL-C4) and the involution `ι`. -/

/-- `D̄`: every crossing switched — the same shadow, the under strand made over -/
def Link.Diagram.switchAll (D : Diagram) : Diagram := D.withOver D.underStrand D.under_mem

theorem Link.Diagram.switchAll_Γ (D : Diagram) : D.switchAll.Γ = D.Γ := rfl

theorem Link.Diagram.switchAll_overStrand (D : Diagram) (x : D.Γ.Crossing) :
    D.switchAll.overStrand x = D.underStrand x := rfl

/-- (U-SW) signs negate, the writhe negates, and a curve carrying `X` carries `X.switchAll`
(`det_swap`, `SignType.sign_neg`) -/
theorem usw_switchAll_sign (D : Diagram) (x : D.Γ.Crossing) : D.switchAll.sign x = -D.sign x := by
  sorry

theorem usw_switchAll_writhe (D : Diagram) : D.switchAll.writhe = -D.writhe := by
  sorry

theorem usw_carried_switchAll (γ : SmoothRegularLoop) (X : Diagram) (c : Carried γ X) :
    Nonempty (Carried γ X.switchAll) := by
  sorry

/-- (U-SW) switching every crossing carries the generators of `LinkEquiv`, the crossing-free circle
and the skein triples (with `D₊`, `D₋` exchanged) — the analogue of the accepted `MirrorCarries` for
the printed `D̄` (`Reparam` needs an under-visit lemma; `RIIData.same_over` swaps arcs; `RIIIData`
is relabelled `(a, b, c) ↦ (c, b, a)`; the oriented smoothing is over-data-free) -/
structure SwitchAllCarriesUnit : Prop where
  planar : ∀ D D' : Diagram, PlanarIsotopic D D' → PlanarIsotopic D.switchAll D'.switchAll
  ri : ∀ D D' : Diagram, RI D D' → RI D.switchAll D'.switchAll
  rii : ∀ D D' : Diagram, RII D D' → RII D.switchAll D'.switchAll
  riii : ∀ D D' : Diagram, RIII D D' → RIII D.switchAll D'.switchAll
  circle : ∀ D : Diagram, D.IsCrossingFreeCircle → D.switchAll.IsCrossingFreeCircle
  skein : ∀ Dp Dm D0 : Diagram, IsSkeinTriple Dp Dm D0 →
    IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll

theorem usw_switchAllCarries : SwitchAllCarriesUnit := by
  sorry

/-- the involutive automorphism `ι : (a, z) ↦ (a⁻¹, −z)` of `R` (sm-3:4540), as the `ℤ`-algebra
homomorphism sending the generators to the units `a⁻¹`, `−z` -/
def iotaHom : R →+* R :=
  (AddMonoidAlgebra.lift ℤ R (ℤ × ℤ) (unitPowers (R.aUnit⁻¹) (-R.zUnit))).toRingHom

/-- (U-ι) what the route reads off `ι`: the generator values, the coefficient law
`[a^d z^k] (ι f) = (−1)^k [a^{−d} z^k] f`, and "the substitution negates every a-exponent and
cannot cancel a nonzero extreme coefficient": `max deg_a (ι f) = −min deg_a f` for `f ≠ 0` -/
structure MirrorSubstitutionData (ι : R →+* R) : Prop where
  ι_a : ι R.a = R.aInv
  ι_aInv : ι R.aInv = R.a
  ι_z : ι R.z = -R.z
  coeff : ∀ (f : R) (d k : ℤ), coeffAt d k (ι f) = (-1) ^ k.toNat * coeffAt (-d) k f
  degAZ_eq : ∀ f : R, f ≠ 0 → degAZ (ι f) = -mindegAZ f
  ne_zero : ∀ f : R, f ≠ 0 → ι f ≠ 0

theorem ui_mirrorSubstitution : MirrorSubstitutionData iotaHom := by
  sorry

/-- (U-EQ) the mirror identity `P_{D̄}(a, z) = P_D(a⁻¹, −z)` (sm-3:4533-4551): `D ↦ ι(P_{D̄})` is an
`RCompetitor` (`usw_switchAllCarries` + lp:core + `ι` a ring hom, the skein "multiplied by −1"), so
`coefficient_transport` identifies it with `P` and `ι` is applied once more (`ι ∘ ι = id`). -/
theorem usw_P_switchAll (X : Diagram) : P X.switchAll = iotaHom (P X) := by
  sorry

/-! ### 8.5 Unit U-ROT: "Rotate coordinates so that u is the downward vertical" (sm-3:4428-4429),
applied to the SMOOTH curve only — legitimate because the record (`RecordCarried`, and the
`HeightMarking` the lift produces) is record-level (FR-FL-C6). -/

/-- the rotation of the plane by the angle `φ` -/
def rotPlane (φ : ℝ) (p : Plane) : Plane :=
  (Real.cos φ * p.1 - Real.sin φ * p.2, Real.sin φ * p.1 + Real.cos φ * p.2)

/-- the downward vertical direction of the `xz` page -/
def downDir : Plane := ((0 : ℝ), (-1 : ℝ))

/-- (U-ROT) a record-carrying regular loop may be rotated so that a given unit direction becomes the
downward vertical; the polygonal record is untouched (`det` is rotation-invariant), every unit
tangent is rotated -/
theorem urot_exists_rotated (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X) (u : Plane)
    (hu : euclideanLength u = 1) :
    ∃ (φ : ℝ) (G : SmoothRegularLoop), G.γ = rotPlane φ ∘ F.γ ∧ Nonempty (RecordCarried G X) ∧
      ∀ t, SM.normalize (deriv G.γ t) = downDir ↔ SM.normalize (deriv F.γ t) = u := by
  sorry

/-! ### 8.6 Unit U-CHAIN: the `R` curls (sm-3:4433-4455) -/

/-- (U-CHAIN helper) the subdivision points `a` are monotone on `[0, k]` -/
theorem ucurl_a_mono {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.k) :
    W.a i ≤ W.a j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m him ih =>
    have hm : m < C.k := by omega
    have := ih hm.le
    linarith [W.a_lt_b m hm, W.b_lt_a m hm]

/-- (U-CHAIN helper) `0 ≤ a j` for `j ≤ k` -/
theorem ucurl_a_nonneg {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) {j : ℕ} (hj : j ≤ C.k) : 0 ≤ W.a j := by
  have := ucurl_a_mono W (Nat.zero_le j) hj
  rwa [W.a_zero] at this

/-- (U-CHAIN helper) `b j < 1` for `j < k` -/
theorem ucurl_b_lt_one {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) {j : ℕ} (hj : j < C.k) : W.b j < 1 := by
  have h1 := W.b_lt_a j hj
  have h2 := ucurl_a_mono W (Nat.succ_le_of_lt hj) le_rfl
  rw [W.a_last] at h2
  linarith

/-- (U-CHAIN helper) the closed junction interval lies in the fundamental period `[0, 1)` -/
theorem ucurl_Icc_subset_Ico {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) {j : ℕ} (hj : j < C.k) :
    Set.Icc (W.a j) (W.b j) ⊆ Set.Ico (0 : ℝ) 1 := by
  intro t ht
  exact ⟨(ucurl_a_nonneg W hj.le).trans ht.1, lt_of_le_of_lt ht.2 (ucurl_b_lt_one W hj)⟩

/-- (U-CHAIN helper) a point of the closed junction `i` is not in the open junction `j ≠ i` -/
theorem ucurl_junction_disjoint {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) {i j : ℕ} (hi : i < C.k) (hj : j < C.k)
    (hij : i ≠ j) {t : ℝ} (ht : t ∈ Set.Icc (W.a i) (W.b i)) : t ∉ Set.Ioo (W.a j) (W.b j) := by
  intro ht'
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have h1 := W.b_lt_a i hi
    have h2 := ucurl_a_mono W (Nat.succ_le_of_lt hlt) hj.le
    linarith [ht.2, ht'.1]
  · have h1 := W.b_lt_a j hj
    have h2 := ucurl_a_mono W (Nat.succ_le_of_lt hgt) hi.le
    linarith [ht.1, ht'.2]

/-- (U-CHAIN helper) two parameters of the fundamental period differing by an integer coincide -/
theorem ucurl_int_eq_zero {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℤ}
    (hn : t + n ∈ Set.Ico (0 : ℝ) 1) : n = 0 := by
  have h1 : (n : ℝ) < 1 := by linarith [ht.1, hn.2]
  have h2 : (-1 : ℝ) < n := by linarith [ht.2, hn.1]
  have h1' : n < 1 := by exact_mod_cast h1
  have h2' : -1 < n := by exact_mod_cast h2
  omega

/-- (U-CHAIN helper) a function constant left of `a`, constant right of `b`, antitone on `[a, b]`,
is antitone on `ℝ` (clamping) -/
theorem ucurl_antitone_of_pieces {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hL : ∀ t, t ≤ a → f t = f a) (hR : ∀ t, b ≤ t → f t = f b)
    (hI : AntitoneOn f (Set.Icc a b)) : Antitone f := by
  have hclamp : ∀ t, f t = f (max a (min t b)) := by
    intro t
    rcases le_or_gt t a with h1 | h1
    · rw [hL t h1]
      have : max a (min t b) = a := max_eq_left ((min_le_left t b).trans h1)
      rw [this]
    · rcases le_or_gt b t with h2 | h2
      · rw [hR t h2]
        have : max a (min t b) = b := by rw [min_eq_right h2, max_eq_right hab]
        rw [this]
      · have : max a (min t b) = t := by rw [min_eq_left h2.le, max_eq_right h1.le]
        rw [this]
  intro x y hxy
  rw [hclamp x, hclamp y]
  apply hI
  · exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  · exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  · exact max_le_max le_rfl (min_le_min hxy le_rfl)

/-- (U-CHAIN helper) a positively crossed junction has a positive principal turn (a negative turn
would make the lift antitone on `ℝ`, hence of nonpositive derivative) -/
theorem ucurl_turn_pos {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (hturn : ∀ i, principalTurn C.P i ≠ 0)
    {j : ℕ} (hj : j < C.k) {t₀ : ℝ} (hderiv : 0 < deriv (W.θ j) t₀) :
    0 < principalTurn C.P j := by
  rcases lt_or_gt_of_ne (hturn j) with hneg | hpos
  · exfalso
    have hanti := ((W.θ_strict j hj).2 hneg).antitoneOn
    have hA : Antitone (W.θ j) :=
      ucurl_antitone_of_pieces (W.a_lt_b j hj).le (W.θ_const_left j hj) (W.θ_const_right j hj) hanti
    exact absurd hderiv (not_lt.mpr hA.deriv_nonpos)
  · exact hpos

/-- (U-CHAIN helper) the open Euclidean disc lies in the interior of the closed corner disc -/
theorem ucurl_mem_interior_cornerDisc (C : PolyComp) (ε : ℝ) (i : ZMod C.k) {p : Plane}
    (hp : eucDist p (C.P i) < ε) : p ∈ interior (cornerDisc C ε i) := by
  rw [mem_interior_iff_mem_nhds]
  have hopen : IsOpen {q : Plane | eucDist q (C.P i) < ε} :=
    isOpen_lt (CornerRounding.E_continuous_eucDist _) continuous_const
  exact Filter.mem_of_superset (hopen.mem_nhds hp) (fun q hq => le_of_lt (show eucDist q (C.P i) < ε from hq))

open CornerRounding in
/-- (U-CHAIN helper) interior junction points of the rounding record lie in the interior of the
corner disc (`curveMap_on_junction` + `juncArc_mem_open_disc`) -/
theorem ucurl_junction_mem_interior (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ) (hj : j < C.k) (t : ℝ)
    (ht : t ∈ Set.Ioo ((Round C D ε h).a j) ((Round C D ε h).b j)) :
    (Round C D ε h).Lε.γ t ∈ interior (cornerDisc C ε j) := by
  have hℓ := ℓ_pos h j
  have hΛ := Λ_pos h
  have ht' : t ∈ Set.Ioo (a C ε j) (b C ε j) := ht
  have hs : (t - a C ε j) * Λ C ε / ℓ C ε j ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (mul_pos (sub_pos.mpr ht'.1) hΛ) hℓ
    · rw [div_lt_one hℓ]
      have h1 : t - a C ε j < ℓ C ε j / Λ C ε := by
        have := b_sub_a (C := C) (ε := ε) j
        linarith [ht'.2]
      calc (t - a C ε j) * Λ C ε < (ℓ C ε j / Λ C ε) * Λ C ε := by gcongr
        _ = ℓ C ε j := div_mul_cancel₀ _ hΛ.ne'
  have hmem := juncArc_mem_open_disc (A0 := A0 C ε j) (θu := θu C j) h.ε_pos (turn_bounds h j).1
    (turn_bounds h j).2 hs
  have hA : A0 C ε j + ε • dirOf (θu C j) = C.P j := by
    rw [dirOf_θu D.regular j]
    unfold A0
    exact sub_add_cancel _ _
  rw [hA] at hmem
  show curveMap C ε t ∈ interior (cornerDisc C ε j)
  rw [curveMap_on_junction h hj ⟨ht'.1.le, ht'.2.le⟩]
  exact ucurl_mem_interior_cornerDisc C ε j hmem

/-- (U-CHAIN) the state after the curls at the tangencies `s` (the invariant of the chain,
sm-3:4433-4455): a regular loop `F` carrying the record of a diagram `X` with `P` unchanged, writhe
lowered by `|s|`, all signs negative; `F` is `L_ε` WITH VELOCITY off the used windows, every point of a
used window lies in the used corner disc (`agree`); the `u`-tangencies of `F` are exactly the unused
tangencies of `L_ε` (`no_u`, the direction needed). -/
structure ucurl_ChainState {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (u : Plane) (s : Finset ℝ) where
  F : SmoothRegularLoop
  X : Diagram
  carried : RecordCarried F X
  poly : P X = P D.toDiagram
  writhe : X.writhe = D.toDiagram.writhe - s.card
  neg : ∀ x, X.sign x = -1
  agree : ∀ t : ℝ, (F.γ t = W.Lε.γ t ∧ deriv F.γ t = deriv W.Lε.γ t) ∨
    ∃ t₁ ∈ s, ∃ j : ℕ, j < C.k ∧ t₁ ∈ Set.Ioo (W.a j) (W.b j) ∧
      (∃ n : ℤ, t + n ∈ Set.Ioo (W.a j) (W.b j)) ∧ F.γ t ∈ cornerDisc C ε j
  no_u : ∀ t : ℝ, normalize (deriv F.γ t) = u →
    ∃ t₁ ∈ tangencySet W u, t₁ ∉ s ∧ ∃ n : ℤ, t = t₁ + n

/-- (U-CHAIN) the initial state: the rounding record itself -/
def ucurl_chainState_zero {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (u : Plane)
    (hneg : ∀ x, D.toDiagram.sign x = -1) : ucurl_ChainState W u ∅ where
  F := W.Lε
  X := D.toDiagram
  carried := W.carried.toRecordCarried
  poly := rfl
  writhe := by simp
  neg := hneg
  agree := fun _ => Or.inl ⟨rfl, rfl⟩
  no_u := fun t ht => by
    refine ⟨Int.fract t, ⟨⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩,
      Finset.notMem_empty _, ⟨⌊t⌋, (Int.fract_add_floor t).symm⟩⟩
    show normalize (deriv W.Lε.γ (Int.fract t)) = u
    have hper := W.Lε.toSmoothLoop.deriv_eq_add_int ⌊t⌋ (Int.fract t)
    rw [Int.fract_add_floor] at hper
    rw [← hper]
    exact ht

/-- (U-CHAIN) the one-step lemma: one more curl, at an unused tangency `t₀` (positively crossed, in
the open junction `j`), through `cf_lem_curl.exists_curl` at the site read off the rounding record,
with the curl disc inside `cornerDisc C ε j` -/
theorem ucurl_step {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (hturn : ∀ i, principalTurn C.P i ≠ 0)
    (hint : ∀ j : ℕ, j < C.k → ∀ t ∈ Set.Ioo (W.a j) (W.b j),
      W.Lε.γ t ∈ interior (cornerDisc C ε j))
    (u : Plane) (s : Finset ℝ) (hs : ∀ t ∈ s, t ∈ tangencySet W u)
    (t₀ : ℝ) (ht₀ : t₀ ∈ tangencySet W u) (ht₀s : t₀ ∉ s) (hcross : CrossesPositively W t₀)
    (st : ucurl_ChainState W u s) : Nonempty (ucurl_ChainState W u (insert t₀ s)) := by
  obtain ⟨j, hj, ht₀j, hderiv⟩ := hcross
  have ht₀I : t₀ ∈ Set.Icc (W.a j) (W.b j) := ⟨ht₀j.1.le, ht₀j.2.le⟩
  -- no used tangency lies in the junction `j`
  have hnone : ∀ t₁ ∈ s, t₁ ∉ Set.Icc (W.a j) (W.b j) := by
    intro t₁ h1 h2
    have heq : t₁ = t₀ := W.direction_once j hj h2 ht₀I (by
      show W.T t₁ = W.T t₀
      rw [(hs t₁ h1).2, ht₀.2])
    exact ht₀s (heq ▸ h1)
  -- `F` is `L_ε` with velocity on the closed junction `j`
  have hunch : ∀ t ∈ Set.Icc (W.a j) (W.b j),
      st.F.γ t = W.Lε.γ t ∧ deriv st.F.γ t = deriv W.Lε.γ t := by
    intro t ht
    rcases st.agree t with h | ⟨t₁, ht₁, j', hj', ht₁j', ⟨n, hn⟩, -⟩
    · exact h
    · exfalso
      have hn0 : n = 0 := ucurl_int_eq_zero (ucurl_Icc_subset_Ico W hj ht)
        (ucurl_Icc_subset_Ico W hj' ⟨hn.1.le, hn.2.le⟩)
      subst hn0
      simp only [Int.cast_zero, add_zero] at hn
      by_cases hjj : j = j'
      · subst hjj
        exact hnone t₁ ht₁ ⟨ht₁j'.1.le, ht₁j'.2.le⟩
      · exact ucurl_junction_disjoint W hj hj' hjj ht hn
  have hpos : 0 < principalTurn C.P j := ucurl_turn_pos W hturn hj hderiv
  -- the site
  let S : CurlSite :=
    { F := st.F
      D := st.X
      carried := st.carried
      u := u
      t₀ := t₀
      tangent_at := by rw [(hunch t₀ ht₀I).2]; exact ht₀.2
      α := W.a j
      β := W.b j
      α_lt := ht₀j.1
      lt_β := ht₀j.2
      short := by linarith [ucurl_a_nonneg W hj.le, ucurl_b_lt_one W hj]
      embedded := (W.junction_embedded j hj).congr (fun t ht => (hunch t ht).1.symm)
      no_double := by
        intro v n hn
        have hτ := st.carried.τ_mem v
        have hn0 : n = 0 := ucurl_int_eq_zero hτ (ucurl_Icc_subset_Ico W hj hn)
        subst hn0
        simp only [Int.cast_zero, add_zero] at hn
        -- the point `q` of the junction is a double point of `F`
        have hq : st.F.γ (st.carried.τ v) = W.Lε.γ (st.carried.τ v) := (hunch _ hn).1
        have hqdisc : W.Lε.γ (st.carried.τ v) ∈ cornerDisc C ε j :=
          W.disc_contains_modification j hj _ hn
        have htw := st.carried.twin_eval v
        have hne : st.carried.τ v ≠ st.carried.τ (st.X.twin v) := fun h =>
          st.X.twin_ne v (st.carried.τ_inj h).symm
        have hτ' := st.carried.τ_mem (st.X.twin v)
        rcases st.agree (st.carried.τ (st.X.twin v)) with ⟨h1, -⟩ |
            ⟨t₁, ht₁, j', hj', ht₁j', ⟨m, hm⟩, hdisc'⟩
        · -- the twin is traversed on an unchanged part: `q` is a double point of `L_ε`, hence a
          -- crossing point of `L`, which is not in the corner disc
          have hdp : W.Lε.γ (st.carried.τ v) ∈ SmoothRegularLoop.doublePoints W.Lε.γ :=
            ⟨st.carried.τ v, st.carried.τ (st.X.twin v), hτ, hτ', hne, rfl, by
              rw [← h1, ← htw, hq]⟩
          rw [W.same_double_points] at hdp
          obtain ⟨x, hx⟩ := hdp
          rw [hx] at hqdisc
          exact W.disc_no_double j x hqdisc
        · -- the twin is traversed in a used window: `q` lies in another corner disc
          have hjj : j ≠ j' := by
            rintro rfl
            exact hnone t₁ ht₁ ⟨ht₁j'.1.le, ht₁j'.2.le⟩
          have hjj' : (j : ZMod C.k) ≠ (j' : ZMod C.k) := by
            intro heq
            apply hjj
            have := congrArg ZMod.val heq
            rwa [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hj'] at this
          have hq' : st.F.γ (st.carried.τ (st.X.twin v)) ∈ cornerDisc C ε j := by
            rw [← htw, hq]; exact hqdisc
          exact Set.disjoint_left.mp (W.disc_disjoint _ _ hjj') hq' hdisc'
      θ := W.θ j
      lift := ⟨(W.θ_lift j hj).1, fun t ht => by
        show normalize (deriv st.F.γ t) = _
        rw [(hunch t ht).2]
        exact (W.θ_lift j hj).2 t ht⟩
      turns_pos := (W.θ_strict j hj).1 hpos
      isolated := by
        intro t ht hu
        rw [(hunch t ht).2] at hu
        exact W.direction_once j hj ht ht₀I (by
          show W.T t = W.T t₀
          rw [ht₀.2]; exact hu) }
  have hp : S.p ∈ interior (cornerDisc C ε j) := by
    show st.F.γ t₀ ∈ interior (cornerDisc C ε j)
    rw [(hunch t₀ ht₀I).1]
    exact hint j hj t₀ ht₀j
  obtain ⟨Δ, hΔ, ⟨Wc⟩⟩ := cf_lem_curl.exists_curl S (cornerDisc C ε j) hp
  have hα : S.α = W.a j := rfl
  have hβ : S.β = W.b j := rfl
  refine ⟨⟨Wc.F', Wc.D', Wc.carried', ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Wc.poly_eq.trans st.poly
  · rw [Wc.writhe_eq, Finset.card_insert_of_notMem ht₀s]
    show st.X.writhe - 1 = D.toDiagram.writhe - ((s.card + 1 : ℕ) : ℤ)
    rw [st.writhe]
    push_cast
    ring
  · intro y
    by_cases hy : y = Wc.kink
    · rw [hy]; exact Wc.kink_neg
    · have h1 := Wc.old_sign (Wc.old.symm ⟨y, hy⟩)
      rw [Equiv.apply_symm_apply] at h1
      exact h1.trans (st.neg _)
  · intro t
    by_cases hw : ∀ n : ℤ, t + n ∉ Set.Ioo Wc.s₁ Wc.s₂
    · have e1 := Wc.unchanged t hw
      have e2 := Wc.unchanged_deriv t hw
      rcases st.agree t with ⟨h1, h2⟩ | ⟨t₁, ht₁, j', hj', h3, h4, h5⟩
      · exact Or.inl ⟨e1.trans h1, e2.trans h2⟩
      · exact Or.inr ⟨t₁, Finset.mem_insert_of_mem ht₁, j', hj', h3, h4, e1 ▸ h5⟩
    · push Not at hw
      obtain ⟨n, hn⟩ := hw
      refine Or.inr ⟨t₀, Finset.mem_insert_self _ _, j, hj, ht₀j, ⟨n, ?_⟩, ?_⟩
      · have h1 := Wc.α_le
        have h2 := Wc.le_β
        rw [hα] at h1
        rw [hβ] at h2
        exact ⟨lt_of_le_of_lt h1 hn.1, lt_of_lt_of_le hn.2 h2⟩
      · have hmem : Wc.F'.γ (t + n) ∈ Δ := Wc.new_in_disc _ ⟨hn.1.le, hn.2.le⟩
        rw [Wc.F'.toSmoothLoop.eq_add_int n t] at hmem
        exact hΔ hmem
  · intro t ht
    by_cases hw : ∀ n : ℤ, t + n ∉ Set.Ioo Wc.s₁ Wc.s₂
    · have e2 := Wc.unchanged_deriv t hw
      rw [e2] at ht
      obtain ⟨t₁, ht₁, ht₁s, n, rfl⟩ := st.no_u t ht
      refine ⟨t₁, ht₁, ?_, n, rfl⟩
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with rfl | hmem
      · apply hw (-n)
        rw [Int.cast_neg, add_neg_cancel_right]
        exact ⟨Wc.s₁_lt, Wc.lt_s₂⟩
      · exact ht₁s hmem
    · push Not at hw
      obtain ⟨n, hn⟩ := hw
      exfalso
      have hmem : Wc.F'.γ (t + n) ∈ Δ := Wc.new_in_disc _ ⟨hn.1.le, hn.2.le⟩
      have h1 := Wc.no_u (t + n) hmem
      rw [Wc.F'.toSmoothLoop.deriv_eq_add_int n t] at h1
      exact h1 ht

/-- (U-CHAIN) from the rounding record of an all-negative polygon diagram with `R` positively-crossed
`u`-tangencies, `R` applications of cf:lem-curl (`cf_lem_curl.exists_curl`, sites from the
`RoundingWitness` fields, each disc inside its corner disc `cornerDisc C ε j`, disjoint supports) give
a regular loop carrying a diagram with no `u`-tangency at all, `P` unchanged, writhe lowered by `R`,
every crossing negative -/
theorem ucurl_exists_curled (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (u : Plane) (hu : euclideanLength u = 1) (R : ℕ)
    (hcount : TangencyCount (Round C D ε h) u R)
    (hneg : ∀ x, D.toDiagram.sign x = -1) :
    ∃ (F' : SmoothRegularLoop) (X' : Diagram), Nonempty (RecordCarried F' X') ∧
      (∀ t, SM.normalize (deriv F'.γ t) ≠ u) ∧ P X' = P D.toDiagram ∧
      X'.writhe = D.toDiagram.writhe - R ∧ ∀ x, X'.sign x = -1 := by
  obtain ⟨hfin, hcard, hcross⟩ := hcount
  have hint : ∀ j : ℕ, j < C.k → ∀ t ∈ Set.Ioo ((Round C D ε h).a j) ((Round C D ε h).b j),
      (Round C D ε h).Lε.γ t ∈ interior (cornerDisc C ε j) :=
    fun j hj t ht => ucurl_junction_mem_interior C D ε h j hj t ht
  have key : ∀ s : Finset ℝ, s ⊆ hfin.toFinset →
      Nonempty (ucurl_ChainState (Round C D ε h) u s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨ucurl_chainState_zero _ u hneg⟩
    | insert t₀ s ht₀s ih =>
      intro hsub
      have hs' : s ⊆ hfin.toFinset := (Finset.subset_insert _ _).trans hsub
      obtain ⟨st⟩ := ih hs'
      have ht₀ : t₀ ∈ tangencySet (Round C D ε h) u :=
        hfin.mem_toFinset.mp (hsub (Finset.mem_insert_self _ _))
      exact ucurl_step _ h.turn_ne hint u s (fun t ht => hfin.mem_toFinset.mp (hs' ht)) t₀ ht₀ ht₀s
        (hcross t₀ ht₀) st
  obtain ⟨st⟩ := key hfin.toFinset (subset_refl _)
  refine ⟨st.F, st.X, ⟨st.carried⟩, ?_, st.poly, ?_, st.neg⟩
  · intro t ht
    obtain ⟨t₁, ht₁, ht₁s, -⟩ := st.no_u t ht
    exact ht₁s (hfin.mem_toFinset.mpr ht₁)
  · have hR : hfin.toFinset.card = R := by
      have h1 : ((tangencySet (Round C D ε h) u).ncard : ℝ) = R := hcard
      rw [Set.ncard_eq_toFinset_card _ hfin] at h1
      exact_mod_cast h1
    rw [st.writhe, hR]

/-! ### 8.7 Unit U-LIFT: the transverse lift (sm-3:4456-4523).  Explicit formulas (B): the lift is
`s ↦ (x(s), y(s), z(s))` with `(x, z) = F.γ`, `y = y₀ + Σ_v ψ_v (c_v − y₀)`; the output is read by
row 94 through `TransverseKnot.Reads` (a `HeightMarking`, FR-FL-C8), and its front's writhe is the
polygonal writhe. -/

/-- `y₀ = −x′ / (v + z′)`, `v = |(x′, z′)|` (smooth and periodic since `v + z′ > 0` off downward
vertical tangencies; `z′ − y₀ x′ = v`, display (*)) -/
def liftY0 (γ : ℝ → Plane) (s : ℝ) : ℝ :=
  -(deriv γ s).1 / (euclideanLength (deriv γ s) + (deriv γ s).2)

/-- a `C^∞` 1-periodic bump on the circle, `= 1` at `s₀`, `= 0` at circle distance `≥ δ`, values in
`[0, 1]` (the printed `ψ_j`, realised through `Real.smoothTransition` and `cos` so that periodicity and
smoothness are free; FR-FL-C7) -/
def circBump (δ s₀ s : ℝ) : ℝ :=
  Real.smoothTransition
    ((Real.cos (2 * Real.pi * (s - s₀)) - Real.cos (2 * Real.pi * δ)) / (1 - Real.cos (2 * Real.pi * δ)))

/-- `y = y₀ + Σ_v ψ_v (c_v − y₀)` over the crossing occurrences `v` at parameters `τ v` with the chosen
admissible constants `c v` -/
def liftY (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) : ℝ :=
  liftY0 γ s + ∑ v, circBump δ (τ v) s * (c v - liftY0 γ s)

/-- the lift `s ↦ (x(s), y(s), z(s))` -/
def liftT (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) : Space :=
  ((γ s).1, liftY γ τ c δ s, (γ s).2)

/-- "admissible constants": `z′(s) − c x′(s) > 0` -/
def LiftAdmissible (γ : ℝ → Plane) (s c : ℝ) : Prop := 0 < (deriv γ s).2 - c * (deriv γ s).1

/-- (U-LIFT-2) sm-3:4477-4494: at a negative double point (`det(t_O, t_U) < 0`) of a curve without
downward vertical tangency there are admissible constants `c_O < c_U` — five cases on the signs of
`x′_O, x′_U`, the determinant used only when `x′_O < 0 < x′_U`; vertical branches (`x′ = 0`, hence
`z′ > 0`) impose no constraint (FR-FL-C7) -/
theorem ul_exists_constants (γ : ℝ → Plane) (sO sU : ℝ) (hO : deriv γ sO ≠ 0) (hU : deriv γ sU ≠ 0)
    (hdO : SM.normalize (deriv γ sO) ≠ downDir) (hdU : SM.normalize (deriv γ sU) ≠ downDir)
    (hdet : det (deriv γ sO) (deriv γ sU) < 0) :
    ∃ cO cU : ℝ, cO < cU ∧ LiftAdmissible γ sO cO ∧ LiftAdmissible γ sU cU := by
  sorry

/-- (U-LIFT-3) the transverse lift: a regular loop with no downward vertical tangency carrying an
all-negative diagram `X` lifts to a positive transverse knot whose front is the loop, which reads `X`
(the smaller-`y` over rule realising `X`'s over data: a `HeightMarking` of `K.spatial.projLoop`),
and whose front's writhe is `X`'s -/
theorem ulift_exists_transverse_lift (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X)
    (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (hneg : ∀ x, X.sign x = -1) :
    ∃ K : TransverseKnot, xzOf K.T = F.γ ∧ K.Reads X ∧ K.front.writhe = X.writhe := by
  sorry

/-! ### 8.8 Unit U-C: the assembly of clause (C) (sm-3:4417-4575) with the row-94 bound as hypothesis -/

/-- normalise by (R) (WLOG `AllPosOrOneNeg C.P`), `D̄ := X.switchAll` on `PolygonDiagram.ofDiagram`,
(B) at `ε := ε₁/2`, `ucurl_exists_curled` with `R := rot`, `urot_exists_rotated`,
`ulift_exists_transverse_lift`, `hbound K X_R`, then the degree algebra
`−w − R ≤ −degAZ (P X_R) − 1 = −degAZ (ι (P X)) − 1 = mindegAZ (P X) − 1` (`usw_P_switchAll`,
`ui_mirrorSubstitution.degAZ_eq`, `P_ne_zero`), cast to `ℝ` with `R = |rot|`; `floor_zZero` by
`supp (zZeroPart f) ⊆ supp f` and `mindegAZ_spec` -/
theorem cf_thm_carrierfloor_C_of_bound (hbound : TransverseFrontBound) : CarrierFloorCData := by
  sorry

/-- the row, once row 94 lands (D-F11/D-F14 pattern: the conditional theorem is library material; the
row theorem `SM.cf_thm_carrierfloor : CarrierFloorData := cf_thm_carrierfloor_of_bound (…)` is
declared and mapped only when the hypothesis is discharged) -/
theorem cf_thm_carrierfloor_of_bound (hbound : TransverseFrontBound) : CarrierFloorData where
  clauseR := cf_thm_carrierfloor_R
  clauseA := cf_thm_carrierfloor_A
  clauseB := cf_thm_carrierfloor_B
  clauseC := cf_thm_carrierfloor_C_of_bound hbound

/-! ### 8.9 Unit U-F: thm:floor -/

section Floor

open Carrier

variable {n : ℕ} [NeZero n]

/-- the `a`-floor from clause (C) on `C := carrierPolyComp`, `X := positiveLift` (`positiveLift_Γ` is
`Shadow.single (carrierPolyComp …)` by `rfl`; positivity `positiveLift_isPositive`; turns nonzero
lem:carriers (ii) `ccpCornerPolygon_turn_ne_zero`; the alternative from the turn signs via
`principalTurn_sign` and `principalTurn_reversal`; then `positiveLift_writhe_eq_carrierCrossingCount`,
`carrierRotationInt_cast`, `cornerSlot_cast`, `P_eq_homfly`). -/
theorem uf_a_floor_of_C (hC : CarrierFloorCData) (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (halt : CarrierUniformOrOneDissent hn hP S q) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧
    1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤
      (mindegAZ (cornerHomfly hn hP S q hS) : ℝ) := by
  sorry

/-- the `z`-parity clause from lp:core's knot support (`P_support` with `positiveLift_componentCount = 1`,
`P_eq_homfly`, `mindegZZ_spec`) — provable now -/
theorem uf_z_parity (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS) := by
  sorry

/-- thm:floor from clause (C) (proposed row name `SM.thm_floor`, assembled once row 94 lands) -/
theorem thm_floor_of_C (hC : CarrierFloorCData) : FloorTheoremData where
  a_floor := fun hn P hP S hS q halt => uf_a_floor_of_C hC hn P hP S hS q halt
  z_parity := fun hn P hP S hS q => uf_z_parity hn P hP S hS q

theorem thm_floor_of_bound (hbound : TransverseFrontBound) : FloorTheoremData :=
  thm_floor_of_C (cf_thm_carrierfloor_C_of_bound hbound)

end Floor

end

end SM
