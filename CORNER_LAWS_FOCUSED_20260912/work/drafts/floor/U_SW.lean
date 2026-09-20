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

/-- (U-SW helper) the under strand of `D̄` is the over strand of `D` (the other strand of the
crossing at `D.underStrand x`) -/
theorem usw_switchAll_underStrand (D : Diagram) (x : D.Γ.Crossing) :
    D.switchAll.underStrand x = D.overStrand x := by
  symm
  apply D.Γ.eq_other_of_mem_of_ne x (D.switchAll.over_mem x) (D.over_mem x)
  exact D.over_ne_under x

/-- (U-SW) signs negate, the writhe negates, and a curve carrying `X` carries `X.switchAll`
(`det_swap`, `SignType.sign_neg`) -/
theorem usw_switchAll_sign (D : Diagram) (x : D.Γ.Crossing) : D.switchAll.sign x = -D.sign x := by
  unfold Link.Diagram.sign
  rw [Link.Diagram.switchAll_overStrand, usw_switchAll_underStrand, det_swap, Left.sign_neg]
  rfl

theorem usw_switchAll_writhe (D : Diagram) : D.switchAll.writhe = -D.writhe := by
  show ∑ x : D.Γ.Crossing, ((D.switchAll.sign x : SignType) : ℤ) =
    -∑ x : D.Γ.Crossing, ((D.sign x : SignType) : ℤ)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [usw_switchAll_sign]
  rcases D.sign_eq_one_or_neg_one x with h | h <;> rw [h] <;> rfl

/-- (U-SW helper) the over occurrence of `D̄` at `x` is the under occurrence of `D` -/
theorem usw_overVisit (D : Diagram) (x : D.Γ.Crossing) :
    D.switchAll.overVisit x = D.underVisit x := rfl

/-- (U-SW helper) the under occurrence of `D̄` at `x` is the over occurrence of `D` -/
theorem usw_underVisit (D : Diagram) (x : D.Γ.Crossing) :
    D.switchAll.underVisit x = D.overVisit x := by
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Subtype.ext (usw_switchAll_underStrand D x))

theorem usw_carried_switchAll (γ : SmoothRegularLoop) (X : Diagram) (c : Carried γ X) :
    Nonempty (Carried γ X.switchAll) := by
  refine ⟨⟨c.one, c.τ, c.τ_mem, c.τ_inj, c.τ_eval, c.doubles, c.transverse, c.order, ?_⟩⟩
  show ∀ x : X.Γ.Crossing, SignType.sign (det (deriv γ.γ (c.τ (X.switchAll.overVisit x)))
    (deriv γ.γ (c.τ (X.switchAll.underVisit x)))) = X.switchAll.sign x
  intro x
  rw [usw_underVisit, usw_overVisit, det_swap, Left.sign_neg, c.sign_eq x, usw_switchAll_sign]

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

/-! #### U-SW helpers for `usw_switchAllCarries`.  Template: the accepted `mirrorCarries_*`
(LinkMoves.lean 1391-2062) and `OutsideMatch.switch` / `OrientedSmoothingData.switch` (1926-1990).
Here the shadow is literally unchanged (`switchAll_Γ` is `rfl`), so every geometric field is
inherited by definitional unfolding and only the over data moves: `Reparam` needs the under-visit
lemma `usw_reparam_under`, `RIIData.same_over` swaps the two arcs, `RIIIData` is relabelled
`(a, b, c) ↦ (c, b, a)` with the visit orders flipped by the accepted `beforeOn_swap_iff`, and the
skein triple is transported with `D₊`, `D₋` exchanged. -/

/-- (U-SW helper) a traversal point of a generic diagram evaluating to a crossing point is the
traversal point of one of the two occurrences of that crossing: `tail_off` excludes a vertex,
`no_triple` forces the strand to belong to the crossing, `edgePoint_injective` fixes the parameter -/
theorem usw_exists_visit_of_eval_eq (D : Diagram) (p : D.Γ.Pt) (x : D.Γ.Crossing)
    (h : D.Γ.eval p = D.Γ.crossingPoint x) : ∃ w : D.Γ.Visit, w.1 = x ∧ p = D.visitPt w := by
  obtain ⟨i, j, t, ht0, ht1⟩ := p
  have h' : edgePoint (D.Γ.comp i).P j t = D.Γ.crossingPoint x := h
  obtain ⟨u₀, u₁, hxval, hna, -⟩ := x.2
  have hu₀ : u₀ ∈ x.val := by rw [hxval]; simp
  have hu₁ : u₁ ∈ x.val := by rw [hxval]; simp
  -- the parameter is positive: a vertex on both edges of a crossing contradicts `tail_off`
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      subst heq
      rw [edgePoint_zero] at h'
      have key : ∀ u ∈ x.val, D.Γ.IncidentTail ⟨i, j⟩ u := fun u hu => by
        by_contra hn
        exact D.generic.tail_off ⟨i, j⟩ u hn
          (by show (D.Γ.comp i).P j ∈ D.Γ.seg u; rw [h']; exact D.Γ.crossingPoint_mem x hu)
      obtain ⟨i₀, a₀, b₀, hs₀, hu₀eq, hinc₀⟩ := key u₀ hu₀
      obtain ⟨i₁, a₁, b₁, hs₁, hu₁eq, hinc₁⟩ := key u₁ hu₁
      subst hu₀eq hu₁eq
      rw [Sigma.mk.inj_iff] at hs₀ hs₁
      obtain ⟨hi₀, hj₀⟩ := hs₀
      obtain ⟨hi₁, hj₁⟩ := hs₁
      subst hi₀ hi₁
      have hj₀' := eq_of_heq hj₀
      have hj₁' := eq_of_heq hj₁
      subst hj₀' hj₁'
      apply hna
      refine (D.Γ.adjacent_mk_iff _ b₀ b₁).mpr ?_
      rcases hinc₀ with h₀ | h₀ <;> rcases hinc₁ with h₁ | h₁ <;> rw [h₀, h₁]
      · exact Or.inr (Or.inl (sub_self _))
      · exact Or.inr (Or.inr (by ring))
      · exact Or.inl (by ring)
      · exact Or.inr (Or.inl (sub_self _))
  -- the strand `⟨i, j⟩` belongs to `x`: otherwise three edge interiors meet (`no_triple`)
  have hs : (⟨i, j⟩ : D.Γ.Strand) ∈ x.val := by
    by_contra hn
    have hne₀ : (⟨i, j⟩ : D.Γ.Strand) ≠ u₀ := fun e => hn (by rw [e]; exact hu₀)
    have hne₁ : (⟨i, j⟩ : D.Γ.Strand) ≠ u₁ := fun e => hn (by rw [e]; exact hu₁)
    apply D.generic.no_triple
    refine ⟨u₀, u₁, ⟨i, j⟩, D.Γ.ne_of_not_adjacent hna, hne₁.symm, hne₀.symm,
      D.Γ.crossingPoint x, ⟨⟨D.generic.crossingPoint_mem_interior x hu₀,
        D.generic.crossingPoint_mem_interior x hu₁⟩, ?_⟩⟩
    exact ⟨t, htpos, ht1, h'.symm⟩
  refine ⟨⟨x, ⟨⟨i, j⟩, hs⟩⟩, rfl, ?_⟩
  have hne : edge (D.Γ.comp i).P j ≠ 0 := D.Γ.edge_ne_zero D.generic ⟨i, j⟩
  have hparam : t = D.crossingParam x hs :=
    edgePoint_injective hne (h'.trans (D.crossingParam_spec x hs).2.2)
  exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Subtype.ext hparam)))

/-- (U-SW helper) the point map of a reparametrisation is injective -/
theorem usw_mapPt_injective {D D' : Diagram} (r : ReparamData D D') :
    Function.Injective r.mapPt := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have h' : (⟨r.e i, r.φ i p⟩ : D'.Γ.Pt) = ⟨r.e j, r.φ j q⟩ := h
  rw [Sigma.mk.inj_iff] at h'
  obtain ⟨h1, h2⟩ := h'
  have hij : i = j := r.e.injective h1
  subst hij
  rw [(r.φ i).injective (eq_of_heq h2)]

/-- (U-SW helper, the under-visit lemma of PLAN_FINAL §3 (C)) a reparametrisation carrying the
over occurrence of `x` to that of `x'` carries the under occurrence of `x` to that of `x'`: the
image evaluates to the crossing point of `x'`, so it is an occurrence of `x'`
(`usw_exists_visit_of_eval_eq`), and not the over one by injectivity -/
theorem usw_reparam_under {D D' : Diagram} (r : ReparamData D D') (x : D.Γ.Crossing)
    (x' : D'.Γ.Crossing)
    (hx : r.mapPt (D.visitPt (D.overVisit x)) = D'.visitPt (D'.overVisit x')) :
    r.mapPt (D.visitPt (D.underVisit x)) = D'.visitPt (D'.underVisit x') := by
  have e1 : D'.Γ.eval (r.mapPt (D.visitPt (D.underVisit x))) = D.Γ.crossingPoint x :=
    (r.eval_mapPt _).trans (D.eval_visitPt _)
  have e2 : D.Γ.crossingPoint x = D'.Γ.crossingPoint x' :=
    (D.eval_visitPt (D.overVisit x)).symm.trans
      (((r.eval_mapPt _).symm.trans (congrArg D'.Γ.eval hx)).trans (D'.eval_visitPt _))
  obtain ⟨w, hw, hpw⟩ := usw_exists_visit_of_eval_eq D' _ x' (e1.trans e2)
  rcases D'.visit_eq_over_or_under w with h | h
  · exfalso
    rw [hw] at h
    have h3 : D.visitPt (D.underVisit x) = D.visitPt (D.overVisit x) :=
      usw_mapPt_injective r (hpw.trans ((congrArg D'.visitPt h).trans hx.symm))
    exact D.overVisit_ne_underVisit x (D.visitPt_injective h3).symm
  · rw [hw] at h
    exact hpw.trans (congrArg D'.visitPt h)

/-- (U-SW helper) a reparametrisation of `D` as `D'` is one of `D̄` as `D̄'` (same `e`, `φ`; the
over occurrences of `D̄` are the under occurrences of `D`) -/
def usw_reparamData {D D' : Diagram} (r : ReparamData D D') :
    ReparamData D.switchAll D'.switchAll where
  e := r.e
  φ := r.φ
  between := r.between
  eval_eq := r.eval_eq
  over_map := fun x => by
    obtain ⟨x', hx'⟩ := r.over_map x
    exact ⟨x', usw_reparam_under r x x' hx'⟩
  over_surj := fun x' => by
    obtain ⟨x, hx⟩ := r.over_surj x'
    exact ⟨x, usw_reparam_under r x x' hx⟩

/-- (U-SW helper) the under strand of a re-vertexed diagram is the under strand of the original
(same strand labels) -/
theorem usw_deform_underStrand (D : Diagram) (V : D.Γ.Vertices)
    (hgen : (D.Γ.withVertices V).Generic)
    (hcross : ∀ x : Finset D.Γ.Strand, (D.Γ.withVertices V).IsCrossing x ↔ D.Γ.IsCrossing x)
    (x : (D.Γ.withVertices V).Crossing) :
    (D.deform V hgen hcross).underStrand x = D.underStrand ⟨x.val, (hcross x.val).mp x.2⟩ := by
  symm
  apply (D.Γ.withVertices V).eq_other_of_mem_of_ne x ((D.deform V hgen hcross).over_mem x)
    (D.under_mem ⟨x.val, (hcross x.val).mp x.2⟩)
  exact D.under_ne_over ⟨x.val, (hcross x.val).mp x.2⟩

/-- (U-SW helper) switching every crossing commutes with generic re-vertexing -/
theorem usw_switchAll_deform (D : Diagram) (V : D.Γ.Vertices)
    (hgen : (D.Γ.withVertices V).Generic)
    (hcross : ∀ x : Finset D.Γ.Strand, (D.Γ.withVertices V).IsCrossing x ↔ D.Γ.IsCrossing x)
    (hgen' : (D.switchAll.Γ.withVertices V).Generic)
    (hcross' : ∀ x : Finset D.switchAll.Γ.Strand,
      (D.switchAll.Γ.withVertices V).IsCrossing x ↔ D.switchAll.Γ.IsCrossing x) :
    (D.deform V hgen hcross).switchAll = D.switchAll.deform V hgen' hcross' := by
  apply Diagram.mk_eq_of_overStrand_eq
  funext x
  exact usw_deform_underStrand D V hgen hcross x

/-- (U-SW helper) a generic deformation of `D` into `D'` is one of `D̄` into `D̄'` (same vertex
path; `deform` keeps the over strand by label) -/
def usw_deformData {D D' : Diagram} (d : DeformData D D') :
    DeformData D.switchAll D'.switchAll := by
  obtain ⟨γ, cont, start, gen, cross, rfl⟩ := d
  exact
    { γ := γ
      continuous := cont
      start := start
      generic := gen
      crossings := cross
      stop := usw_switchAll_deform D (γ 1) _ _ _ _ }

/-- (U-SW helper) planar isotopy is carried by the crossing switch -/
theorem usw_planar (D D' : Diagram) (h : PlanarIsotopic D D') :
    PlanarIsotopic D.switchAll D'.switchAll :=
  eqvGen_carries Diagram.switchAll (fun E E' => Link.Reparam E E' ∨ Link.Deform E E')
    (fun _ _ hEE' => hEE'.elim (fun hr => Or.inl (hr.elim fun r => ⟨usw_reparamData r⟩))
      (fun hd => Or.inr (hd.elim fun d => ⟨usw_deformData d⟩))) h

theorem usw_clean {U : Set Plane} {D : Diagram} (h : Clean U D) : Clean U D.switchAll :=
  ⟨h.frontier_injOn, h.exits⟩

theorem usw_localFrame {U : Set Plane} {D D' : Diagram} (h : LocalFrame U D D') :
    LocalFrame U D.switchAll D'.switchAll :=
  ⟨h.disc, usw_clean h.clean, usw_clean h.clean'⟩

/-- (U-SW helper) an outside match transports to the switched diagrams (over and under
occurrences exchanged) -/
def usw_outsideMatch {U : Set Plane} {D D' : Diagram} (m : OutsideMatch U D D') :
    OutsideMatch U D.switchAll D'.switchAll where
  φ := m.φ
  eval_eq := m.eval_eq
  dir_pos := m.dir_pos
  dir_pos_before := m.dir_pos_before
  ψ := m.ψ
  over_eq := fun x => m.under_eq x
  under_eq := fun x => by
    have h1 : D.switchAll.outerUnderPt x = D.outerOverPt x :=
      Subtype.ext (congrArg D.visitPt (usw_underVisit D x.1))
    have h2 : D'.switchAll.outerUnderPt (m.ψ x) = D'.outerOverPt (m.ψ x) :=
      Subtype.ext (congrArg D'.visitPt (usw_underVisit D' _))
    exact (congrArg m.φ h1).trans ((m.over_eq x).trans h2.symm)

def usw_moveMatch {U : Set Plane} {D D' : Diagram} (m : MoveMatch U D D') :
    MoveMatch U D.switchAll D'.switchAll :=
  { usw_outsideMatch m.toOutsideMatch with
    e := m.e
    comp_eq := m.comp_eq }

theorem usw_overOn (D : Diagram) (a : D.Γ.Arc) (x : D.Γ.Crossing) :
    D.switchAll.OverOn a x ↔ D.UnderOn a x := Iff.rfl

theorem usw_underOn (D : Diagram) (a : D.Γ.Arc) (x : D.Γ.Crossing) :
    D.switchAll.UnderOn a x ↔ D.OverOn a x := by
  show a.Mem (D.switchAll.visitPt (D.switchAll.underVisit x)) ↔ a.Mem (D.visitPt (D.overVisit x))
  rw [usw_underVisit]
  exact Iff.rfl

theorem usw_separates (D : Diagram) (a b : D.Γ.Arc) (x : D.Γ.Crossing) :
    D.switchAll.Separates a b x ↔ D.Separates a b x := by
  unfold Link.Diagram.Separates
  rw [usw_overOn, usw_overOn, usw_underOn, usw_underOn]
  tauto

theorem usw_beforeOn (D : Diagram) (a : D.Γ.Arc) (x y : D.Γ.Crossing) :
    D.switchAll.BeforeOn a x y ↔ D.BeforeOn a x y := Iff.rfl

/-- (U-SW helper) at a crossing between two disjoint arcs, if the over occurrence is on `a` the
under occurrence is on `b` -/
theorem usw_underOn_of_overOn {U : Set Plane} {D : Diagram} {A : Set D.Γ.Arc}
    (cover : D.Γ.ArcCover U A) {a b : D.Γ.Arc} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {x : D.Γ.Crossing} (sep : D.Separates a b x) (hov : D.OverOn a x) : D.UnderOn b x := by
  rcases sep with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact (cover.disjoint a ha b hb hab _ hov h).elim

theorem usw_triple_comm {α : Type*} (a b c : α) : ({c, b, a} : Set α) = {a, b, c} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- (U-SW helper) a Reidemeister I site transports (the kink's sign is not part of the data) -/
def usw_riData {U : Set Plane} {D D' : Diagram} (h : RIData U D D') :
    RIData U D.switchAll D'.switchAll where
  frame := usw_localFrame h.frame
  out := usw_moveMatch h.out
  a := h.a
  a' := h.a'
  cover := h.cover
  cover' := h.cover'
  start_eq := h.start_eq
  stop_eq := h.stop_eq
  no_inner := h.no_inner
  kink := h.kink
  inner_iff' := h.inner_iff'

theorem usw_ri_carries {D D' : Diagram} (h : RI D D') : RI D.switchAll D'.switchAll := by
  obtain ⟨U, h | h⟩ := h
  · exact ⟨U, Or.inl ⟨usw_riData h.some⟩⟩
  · exact ⟨U, Or.inr ⟨usw_riData h.some⟩⟩

/-- (U-SW helper) a Reidemeister II site transports: the common over strand of `D̄'` is the other
arc (`same_over` swaps `a' ↔ b'`) -/
def usw_riiData {U : Set Plane} {D D' : Diagram} (h : RIIData U D D') :
    RIIData U D.switchAll D'.switchAll where
  frame := usw_localFrame h.frame
  out := usw_moveMatch h.out
  a := h.a
  b := h.b
  a' := h.a'
  b' := h.b'
  ab := h.ab
  ab' := h.ab'
  cover := h.cover
  cover' := h.cover'
  a_start := h.a_start
  a_stop := h.a_stop
  b_start := h.b_start
  b_stop := h.b_stop
  no_inner := h.no_inner
  x₁ := h.x₁
  x₂ := h.x₂
  ne := h.ne
  inner_iff' := h.inner_iff'
  sep₁ := (usw_separates D' _ _ _).mpr h.sep₁
  sep₂ := (usw_separates D' _ _ _).mpr h.sep₂
  same_over := by
    have ha' : h.a' ∈ ({h.a', h.b'} : Set D'.Γ.Arc) := by simp
    have hb' : h.b' ∈ ({h.a', h.b'} : Set D'.Γ.Arc) := by simp
    rw [usw_overOn, usw_overOn, usw_overOn, usw_overOn]
    rcases h.same_over with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨usw_underOn_of_overOn h.cover' ha' hb' h.ab' h.sep₁ h1,
        usw_underOn_of_overOn h.cover' ha' hb' h.ab' h.sep₂ h2⟩
    · exact Or.inl ⟨usw_underOn_of_overOn h.cover' hb' ha' h.ab'.symm h.sep₁.symm h1,
        usw_underOn_of_overOn h.cover' hb' ha' h.ab'.symm h.sep₂.symm h2⟩

theorem usw_rii_carries {D D' : Diagram} (h : RII D D') : RII D.switchAll D'.switchAll := by
  obtain ⟨U, h | h⟩ := h
  · exact ⟨U, Or.inl ⟨usw_riiData h.some⟩⟩
  · exact ⟨U, Or.inr ⟨usw_riiData h.some⟩⟩

/-- (U-SW helper) a Reidemeister III site transports with the height order reversed: the arcs are
relabelled `(a, b, c) ↦ (c, b, a)`, the crossings `xab ↔ xbc`, the over bits `top_* / mid_*`
follow from `Separates` + disjointness, and the three visit-order clauses are flipped with the
accepted `beforeOn_swap_iff` -/
def usw_riiiData {U : Set Plane} {D D' : Diagram} (h : RIIIData U D D') :
    RIIIData U D.switchAll D'.switchAll where
  frame := usw_localFrame h.frame
  out := usw_moveMatch h.out
  a := h.c
  b := h.b
  c := h.a
  a' := h.c'
  b' := h.b'
  c' := h.a'
  ab := h.bc.symm
  bc := h.ab.symm
  ac := h.ac.symm
  ab' := h.bc'.symm
  bc' := h.ab'.symm
  ac' := h.ac'.symm
  cover := (congrArg (D.Γ.ArcCover U) (usw_triple_comm h.a h.b h.c)).mpr h.cover
  cover' := (congrArg (D'.Γ.ArcCover U) (usw_triple_comm h.a' h.b' h.c')).mpr h.cover'
  a_start := h.c_start
  a_stop := h.c_stop
  b_start := h.b_start
  b_stop := h.b_stop
  c_start := h.a_start
  c_stop := h.a_stop
  xab := h.xbc
  xac := h.xac
  xbc := h.xab
  xab_ne_xac := h.xac_ne_xbc.symm
  xab_ne_xbc := h.xab_ne_xbc.symm
  xac_ne_xbc := h.xab_ne_xac.symm
  inner_iff := fun y => (h.inner_iff y).trans (by tauto)
  sep_ab := (usw_separates D _ _ _).mpr h.sep_bc.symm
  sep_ac := (usw_separates D _ _ _).mpr h.sep_ac.symm
  sep_bc := (usw_separates D _ _ _).mpr h.sep_ab.symm
  xab' := h.xbc'
  xac' := h.xac'
  xbc' := h.xab'
  xab_ne_xac' := h.xac_ne_xbc'.symm
  xab_ne_xbc' := h.xab_ne_xbc'.symm
  xac_ne_xbc' := h.xab_ne_xac'.symm
  inner_iff' := fun y => (h.inner_iff' y).trans (by tauto)
  sep_ab' := (usw_separates D' _ _ _).mpr h.sep_bc'.symm
  sep_ac' := (usw_separates D' _ _ _).mpr h.sep_ac'.symm
  sep_bc' := (usw_separates D' _ _ _).mpr h.sep_ab'.symm
  top_ab := (usw_overOn D _ _).mpr
    (usw_underOn_of_overOn h.cover (by simp) (by simp) h.bc h.sep_bc h.mid_bc)
  top_ac := (usw_overOn D _ _).mpr
    (usw_underOn_of_overOn h.cover (by simp) (by simp) h.ac h.sep_ac h.top_ac)
  mid_bc := (usw_overOn D _ _).mpr
    (usw_underOn_of_overOn h.cover (by simp) (by simp) h.ab h.sep_ab h.top_ab)
  top_ab' := (usw_overOn D' _ _).mpr
    (usw_underOn_of_overOn h.cover' (by simp) (by simp) h.bc' h.sep_bc' h.mid_bc')
  top_ac' := (usw_overOn D' _ _).mpr
    (usw_underOn_of_overOn h.cover' (by simp) (by simp) h.ac' h.sep_ac' h.top_ac')
  mid_bc' := (usw_overOn D' _ _).mpr
    (usw_underOn_of_overOn h.cover' (by simp) (by simp) h.ab' h.sep_ab' h.top_ab')
  rev_a := by
    have hxac : D.Γ.crossingPoint h.xac ∈ interior U := (h.inner_iff _).mpr (Or.inr (Or.inl rfl))
    have hxbc : D.Γ.crossingPoint h.xbc ∈ interior U := (h.inner_iff _).mpr (Or.inr (Or.inr rfl))
    have hxac' : D'.Γ.crossingPoint h.xac' ∈ interior U :=
      (h.inner_iff' _).mpr (Or.inr (Or.inl rfl))
    have hxbc' : D'.Γ.crossingPoint h.xbc' ∈ interior U :=
      (h.inner_iff' _).mpr (Or.inr (Or.inr rfl))
    rw [usw_beforeOn, usw_beforeOn,
      D.beforeOn_swap_iff h.cover (by simp) (by simp) (by simp) h.ac.symm h.bc.symm h.xac_ne_xbc
        hxac hxbc h.sep_ac.symm h.sep_bc.symm,
      D'.beforeOn_swap_iff h.cover' (by simp) (by simp) (by simp) h.bc'.symm h.ac'.symm
        h.xac_ne_xbc'.symm hxbc' hxac' h.sep_bc'.symm h.sep_ac'.symm]
    exact not_congr h.rev_c
  rev_b := by
    have hxab : D.Γ.crossingPoint h.xab ∈ interior U := (h.inner_iff _).mpr (Or.inl rfl)
    have hxbc : D.Γ.crossingPoint h.xbc ∈ interior U := (h.inner_iff _).mpr (Or.inr (Or.inr rfl))
    have hxab' : D'.Γ.crossingPoint h.xab' ∈ interior U := (h.inner_iff' _).mpr (Or.inl rfl)
    have hxbc' : D'.Γ.crossingPoint h.xbc' ∈ interior U :=
      (h.inner_iff' _).mpr (Or.inr (Or.inr rfl))
    rw [usw_beforeOn, usw_beforeOn,
      D.beforeOn_swap_iff h.cover (by simp) (by simp) (by simp) h.ab.symm h.bc h.xab_ne_xbc
        hxab hxbc h.sep_ab.symm h.sep_bc,
      D'.beforeOn_swap_iff h.cover' (by simp) (by simp) (by simp) h.bc' h.ab'.symm
        h.xab_ne_xbc'.symm hxbc' hxab' h.sep_bc' h.sep_ab'.symm]
    exact not_congr h.rev_b
  rev_c := by
    have hxab : D.Γ.crossingPoint h.xab ∈ interior U := (h.inner_iff _).mpr (Or.inl rfl)
    have hxac : D.Γ.crossingPoint h.xac ∈ interior U := (h.inner_iff _).mpr (Or.inr (Or.inl rfl))
    have hxab' : D'.Γ.crossingPoint h.xab' ∈ interior U := (h.inner_iff' _).mpr (Or.inl rfl)
    have hxac' : D'.Γ.crossingPoint h.xac' ∈ interior U :=
      (h.inner_iff' _).mpr (Or.inr (Or.inl rfl))
    rw [usw_beforeOn, usw_beforeOn,
      D.beforeOn_swap_iff h.cover (by simp) (by simp) (by simp) h.ab h.ac h.xab_ne_xac
        hxab hxac h.sep_ab h.sep_ac,
      D'.beforeOn_swap_iff h.cover' (by simp) (by simp) (by simp) h.ac' h.ab'
        h.xab_ne_xac'.symm hxac' hxab' h.sep_ac' h.sep_ab']
    exact not_congr h.rev_a

theorem usw_riii_carries {D D' : Diagram} (h : RIII D D') : RIII D.switchAll D'.switchAll := by
  obtain ⟨U, h | h⟩ := h
  · exact ⟨U, Or.inl ⟨usw_riiiData h.some⟩⟩
  · exact ⟨U, Or.inr ⟨usw_riiiData h.some⟩⟩

/-- (U-SW helper) a smoothing site of `D` at `x` is one of `D̄` at `x` with the two arcs exchanged
(the oriented smoothing is over-data-free; template `OrientedSmoothingData.switch`) -/
def usw_orientedSmoothingData {U : Set Plane} {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram}
    (h : OrientedSmoothingData U D x D₀) :
    OrientedSmoothingData U D.switchAll x D₀.switchAll where
  frame := usw_localFrame h.frame
  center := h.center
  out := usw_outsideMatch h.out
  a := h.b
  b := h.a
  ab := h.ab.symm
  cover := by
    have := h.cover
    rwa [Set.pair_comm] at this
  over_on_a := (usw_overOn D _ _).mpr h.under_on_b
  under_on_b := (usw_underOn D _ _).mpr h.over_on_a
  inner_iff := h.inner_iff
  a₀ := h.b₀
  b₀ := h.a₀
  ab₀ := h.ab₀.symm
  cover₀ := by
    have := h.cover₀
    rwa [Set.pair_comm] at this
  no_inner₀ := h.no_inner₀
  a₀_start := h.b₀_start
  a₀_stop := h.b₀_stop
  b₀_start := h.a₀_start
  b₀_stop := h.a₀_stop

theorem usw_isOrientedSmoothing {D : Diagram} {x : D.Γ.Crossing} {D₀ : Diagram}
    (h : IsOrientedSmoothing D x D₀) : IsOrientedSmoothing D.switchAll x D₀.switchAll := by
  obtain ⟨U, h⟩ := h
  exact ⟨U, ⟨usw_orientedSmoothingData h.some⟩⟩

/-- (U-SW helper) `D̄₊ = (D₋)‾ switched at `x`: the switch of every crossing of the switch at `x` -/
theorem usw_switchAll_eq_switch (Dp : Diagram) (x : Dp.Γ.Crossing) :
    Dp.switchAll = (Dp.switch x).switchAll.switch x := by
  apply Diagram.mk_eq_of_overStrand_eq
  funext y
  show Dp.switchAll.overStrand y = ((Dp.switch x).switchAll.switch x).overStrand y
  by_cases hy : y = x
  · rw [hy]
    have e1 : ((Dp.switch x).switchAll.switch x).overStrand x =
        (Dp.switch x).switchAll.underStrand x :=
      (Dp.switch x).switchAll.switch_overStrand_self x
    have e2 : (Dp.switch x).switchAll.underStrand x = (Dp.switch x).overStrand x :=
      usw_switchAll_underStrand (Dp.switch x) x
    have e3 : (Dp.switch x).overStrand x = Dp.underStrand x := Dp.switch_overStrand_self x
    exact (e1.trans (e2.trans e3)).symm
  · have e1 : ((Dp.switch x).switchAll.switch x).overStrand y =
        (Dp.switch x).switchAll.overStrand y :=
      (Dp.switch x).switchAll.switch_overStrand_of_ne hy
    have e2 : (Dp.switch x).switchAll.overStrand y = (Dp.switch x).underStrand y := rfl
    have e3 : (Dp.switch x).underStrand y = Dp.underStrand y := Dp.switch_underStrand_of_ne hy
    exact (e1.trans (e2.trans e3)).symm

/-- (U-SW helper) the crossing switch exchanges the two sides of every skein triple (the crossing
`x` is negative in `D₋`, hence positive in `D̄₋`; the smoothing is over-data-free) -/
theorem usw_skein {Dp Dm D0 : Diagram} (h : IsSkeinTriple Dp Dm D0) :
    IsSkeinTriple Dm.switchAll Dp.switchAll D0.switchAll := by
  obtain ⟨x, hx, rfl, hs⟩ := h
  refine ⟨x, ?_, usw_switchAll_eq_switch Dp x, usw_isOrientedSmoothing hs.switch⟩
  have h1 : (Dp.switch x).switchAll.sign x = Dp.sign x :=
    (usw_switchAll_sign (Dp.switch x) x).trans
      ((congrArg Neg.neg (Dp.switch_sign_self x)).trans (neg_neg _))
  exact ((Dp.switch x).switchAll.isPositive_iff_sign_eq_one x).mpr
    (h1.trans ((Dp.isPositive_iff_sign_eq_one x).mp hx))

theorem usw_switchAllCarries : SwitchAllCarriesUnit := by
  exact
    { planar := usw_planar
      ri := fun _ _ h => usw_ri_carries h
      rii := fun _ _ h => usw_rii_carries h
      riii := fun _ _ h => usw_riii_carries h
      circle := fun _ h => ⟨h.1, h.2⟩
      skein := fun _ _ _ h => usw_skein h }

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
  sorry

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
