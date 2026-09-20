-- Ported %s 2026-09-15 from work/drafts/floor/Floor_Assembled.lean (rows 99 cf:thm-carrierfloor and 100 thm:floor: statements, the 23 proved leaves of waves 1-2 with their prefixed helpers, the conditional assemblies) by the pod executor; body verbatim except this header, the module docstring paragraph on the draft state, §1 (the two `TransverseKnot.spatial` / `spatial_T` copies removed — accepted in SM/SrcContact.lean — and its docstring reworded), the §8 heading, the `TransverseFrontBound` docstring, and the new §9 (the hypothesis discharged from the accepted row 94). D-FL-4: `MirrorSubstitutionData.coeff` carries `(-1) ^ k.natAbs` (repaired after a kernel-checked refutation of the draft's `k.toNat`, see AUTHOR_NOTES).
import SM.Curl
import SM.TransverseFront
import SM.CeSmoothingRecord
import SM.CornerStateSum
import SM.LinkPositiveLift
import SM.UniformRotation
import SM.FdContactUnits

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

Every leaf of the proof route (§8) is proved (waves 1 and 2, work/drafts/floor/FLOOR_ASSEMBLY_REPORT.md);
the conditional row theorems `cf_thm_carrierfloor_of_bound` and `thm_floor_of_bound` are proved from them, and §9
discharges the hypothesis from the accepted row 94 (`SM.fd_contact`, SM/FdContactUnits.lean).  The row theorems
`SM.cf_thm_carrierfloor` and `SM.thm_floor` are declared in SM/CarrierFloorRows.lean.  Also consumed:
SM/SrcContact.lean (`TransverseKnot.spatial`, `SM.sl`), SM/FdContactStatements.lean (`FdContactData`).

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

`TransverseKnot.spatial` is the accepted definition of SM/SrcContact.lean (D-SC-5; the contact lane's
module landed 15:07Z, so the draft's verbatim copy is not repeated here); `TransverseKnot.Reads` is defined
here (the accepted `FdContactData.representative_bound` spells the same reading out inline).  Both contact designs state
fd:contact as `FdContactData` with fields `front_writhe : sl K = ↑K.front.writhe` and
`representative_bound : K.Reads X → sl K ≤ −↑(degAZ (P X)) − 1`; `FdContactShape sl` is exactly that
pair, and `TransverseFrontBound` is their sl-free composite, the ONLY thing clause (C) consumes
(sm-3:4525-4531: "By Theorem fd:contact, sl(K_T) = w(T) = −w − R … max deg_a P_{D̄} ≤ −sl(K_T) − 1"). -/


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
route, discharged in §9 from the accepted row 94 (`SM.fd_contact`): "for every transverse knot `K` and every polygonal reading `X` of its
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

/-- (U-A helper) the closed interval `[a, b]` is the image of `[0, 1]` under the affine map
`s ↦ a + s (b − a)` -/
theorem ua_Icc_eq_image_affine {a b : ℝ} (hab : a < b) :
    Set.Icc a b = (fun s : ℝ => a + s * (b - a)) '' Set.Icc (0 : ℝ) 1 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  ext t
  constructor
  · intro ht
    refine ⟨(t - a) / (b - a), ⟨div_nonneg (sub_nonneg.mpr ht.1) hba.le,
      (div_le_one₀ hba).mpr (by linarith [ht.2])⟩, ?_⟩
    simp only
    rw [div_mul_cancel₀ _ hba.ne']
    ring
  · rintro ⟨s, hs, rfl⟩
    constructor
    · nlinarith [hs.1, hba]
    · nlinarith [hs.2, hba]

/-- (U-A helper) the junction image of a record on `[a j, b j]` is the image of the template
`junctionTemplate q_j u_j v_j ε` on `[0, 1]` (`junction_determined` + the affine reparametrisation) -/
theorem ua_image_junction (hA : CarrierFloorAData) (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ) (hj : j < C.k) :
    (Round C D ε h).Lε.γ '' Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) =
      junctionTemplate (C.P j) (CornerRounding.uDir C j) (CornerRounding.vDir C j) ε ''
        Set.Icc (0 : ℝ) 1 := by
  rw [ua_Icc_eq_image_affine ((Round C D ε h).a_lt_b j hj), Set.image_image]
  exact Set.image_congr fun s hs => hA.junction_determined C D ε h j hj s hs

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
  rw [ua_image_junction hA C D ε h j hj, ua_image_junction hA C' D' ε h' j' hj', hq, hu, hv]

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
  -- (assembler, wave 1) `floor` + `mindegAZ_spec` on `P X ≠ 0` (`P_ne_zero`)
  have h1 := hC.floor C X h
  have h2 : mindegAZ (P X) ≤ d := (mindegAZ_spec (P_ne_zero X)).2 d k hdk
  have h3 : (mindegAZ (P X) : ℝ) ≤ (d : ℝ) := by exact_mod_cast h2
  linarith

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

/-! ## 8. The proof route: frozen unit statements (all leaves proved; prefixes per PLAN_FINAL.md §4).
Every unit file is a byte-identical copy of this file plus proofs of its leaves and prefixed helpers;
an assembler merges (the curl-lane pattern). -/

/-! ### 8.1 Unit U-R: reversal (lp:coefficient-transport + `ReverseCarries` + `IsSkeinTriple.reverse`) -/

/-- U-R helper: reversal keeps the crossing-free circle.  `c` is unchanged (`Diagram.reverse_componentCount`
is `rfl`) and the crossings of `X.reverse.Γ = X.Γ.reverseShadow` are in bijection with those of `X.Γ`
(`Shadow.reverseCrossingEquiv`, LinkDiagram.lean:1199), so emptiness transports. -/
theorem ur_isCrossingFreeCircle_reverse (D : Diagram) (h : D.IsCrossingFreeCircle) :
    D.reverse.IsCrossingFreeCircle := by
  obtain ⟨hc, hemp⟩ := h
  refine ⟨hc, ?_⟩
  exact D.Γ.reverseCrossingEquiv.isEmpty

/-- U-R helper: `D ↦ P_{−D}` satisfies the hypotheses of lp:coefficient-transport (`RCompetitor`,
CoefficientTransport.lean:23): planar isotopy and the three Reidemeister moves are carried by reversal
(`reverseCarries_planarIsotopic/RI/RII/RIII`, LinkMoves.lean:2459/3071/3117/3231) and `P` is invariant
under them (`P_planar`, `P_reidemeister_*`, PolynomialBlock.lean:604-607); the crossing-free circle is
carried (`ur_isCrossingFreeCircle_reverse`) and `P_circle` (609); skein triples are carried with the sides
kept (`IsSkeinTriple.reverse`, LinkMoves.lean:3318) and `P_skein` (638). -/
theorem ur_reverse_rcompetitor : RCompetitor (fun D : Diagram => P D.reverse) where
  planar := fun D D' h => P_planar (reverseCarries_planarIsotopic D D' h)
  reidemeister_I := fun D D' h => P_reidemeister_I (reverseCarries_RI D D' h)
  reidemeister_II := fun D D' h => P_reidemeister_II (reverseCarries_RII D D' h)
  reidemeister_III := fun D D' h => P_reidemeister_III (reverseCarries_RIII D D' h)
  circle := fun D h => P_circle (ur_isCrossingFreeCircle_reverse D h)
  skein := fun _ _ _ h => P_skein h.reverse

/-- `D ↦ P_{−D}` is an `RCompetitor` (accepted `reverseCarries_planarIsotopic/RI/RII/RIII`,
`IsSkeinTriple.reverse`, the crossing-free circle is carried); hence `P X.reverse = P X` for EVERY
link diagram (the printed proof argues "on all oriented link diagrams"; the row states the knot case). -/
theorem ur_P_reverse_all (X : Diagram) : P X.reverse = P X :=
  congrFun (coefficient_transport (fun D : Diagram => P D.reverse) P ur_reverse_rcompetitor
    P_rcompetitor) X

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

/-- (U-A helper) `dirOf` respects a common shift: equal directions stay equal after adding `x`
(`planeComplex (dirOf α) = e^{iα}`, `Complex.exp_add`) -/
theorem ua_dirOf_add_congr {α β : ℝ}
    (hαβ : CornerRounding.dirOf α = CornerRounding.dirOf β) (x : ℝ) :
    CornerRounding.dirOf (α + x) = CornerRounding.dirOf (β + x) := by
  apply planeComplex_injective
  have h := congrArg planeComplex hαβ
  rw [CornerRounding.G1_planeComplex_dirOf, CornerRounding.G1_planeComplex_dirOf] at h
  rw [CornerRounding.G1_planeComplex_dirOf, CornerRounding.G1_planeComplex_dirOf]
  push_cast
  rw [add_mul, Complex.exp_add, add_mul, Complex.exp_add, h]

/-- (U-A helper) the junction arc depends on its start angle only through the direction
`dirOf θu` (the `2π`-periodicity of `juncArc` in `θu`) -/
theorem ua_juncArc_congr {A0 : Plane} {ε θ θ' ϑ s : ℝ}
    (hθ : CornerRounding.dirOf θ = CornerRounding.dirOf θ') :
    CornerRounding.juncArc A0 ε θ ϑ s = CornerRounding.juncArc A0 ε θ' ϑ s := by
  unfold CornerRounding.juncArc
  congr 2
  exact intervalIntegral.integral_congr fun r _ => ua_dirOf_add_congr hθ _

/-- (U-A helper) the direction of the argument of the unit vector `u_j` is `u_j` itself
(`G1_smul_dirOf_arg` with `|u_j| = 1`) -/
theorem ua_dirOf_arg_uDir (C : PolyComp) (hreg : Regular C.P) (j : ZMod C.k) :
    CornerRounding.dirOf (Complex.arg (planeComplex (CornerRounding.uDir C j))) =
      CornerRounding.uDir C j := by
  have h1 : euclideanLength (CornerRounding.uDir C j) = 1 :=
    euclideanLength_normalize (hreg j).1
  have h := CornerRounding.G1_smul_dirOf_arg (CornerRounding.uDir C j)
  rwa [h1, one_smul] at h

/-- (U-A helper) the principal angle is invariant under positive rescaling of both vectors
(`cornerRotor (r u) (r' v) = r r' cornerRotor u v`, `Complex.arg_real_mul`) -/
theorem ua_principalAngle_smul {u v : Plane} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    principalAngle (r • u) (r' • v) = principalAngle u v := by
  have e : cornerRotor (r • u) (r' • v) = ((r * r' : ℝ) : ℂ) * cornerRotor u v := by
    unfold cornerRotor
    rw [planeComplex_smul, planeComplex_smul, Complex.real_smul, Complex.real_smul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  unfold principalAngle
  rw [e, Complex.arg_real_mul _ (mul_pos hr hr')]

/-- (U-A helper) the principal angle from `u_j` to `v_j` is the principal turn `ϑ_j`
(`u_j`, `v_j` are the positive rescalings of the incident edges) -/
theorem ua_principalAngle_uDir_vDir (C : PolyComp) (hreg : Regular C.P) (j : ZMod C.k) :
    principalAngle (CornerRounding.uDir C j) (CornerRounding.vDir C j) = CornerRounding.turn C j := by
  unfold CornerRounding.uDir CornerRounding.vDir CornerRounding.turn principalTurn normalize
  exact ua_principalAngle_smul (inv_pos.mpr (euclideanLength_pos (hreg j).1))
    (inv_pos.mpr (euclideanLength_pos (hreg j).2.1))

/-- `curveMap_on_junction` (Rounding.lean:1668) + `dirOf_θu` (1207) + `G1_dirOf_arg` (1172) +
scale invariance of `principalAngle` (`Complex.arg_real_mul` on `cornerRotor`) + `2π`-periodicity of
`juncArc` in its `θu` argument -/
theorem ua_junction_determined (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ) (hj : j < C.k) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (Round C D ε h).Lε.γ ((Round C D ε h).a j + s * ((Round C D ε h).b j - (Round C D ε h).a j)) =
      junctionTemplate (C.P j) (CornerRounding.uDir C j) (CornerRounding.vDir C j) ε s := by
  have hreg : Regular C.P := D.regular
  have hab := CornerRounding.a_lt_b h j
  have ht : CornerRounding.a C ε j + s * (CornerRounding.b C ε j - CornerRounding.a C ε j) ∈
      Set.Icc (CornerRounding.a C ε j) (CornerRounding.b C ε j) :=
    ⟨by nlinarith [hs.1, hab], by nlinarith [hs.2, hab]⟩
  show CornerRounding.curveMap C ε
      (CornerRounding.a C ε j + s * (CornerRounding.b C ε j - CornerRounding.a C ε j)) = _
  rw [CornerRounding.curveMap_on_junction h hj ht, add_sub_cancel_left, mul_assoc, mul_div_assoc,
    CornerRounding.G2_arg_b h j, mul_one]
  unfold junctionTemplate
  rw [ua_principalAngle_uDir_vDir C hreg j]
  exact ua_juncArc_congr
    ((CornerRounding.dirOf_θu hreg j).trans (ua_dirOf_arg_uDir C hreg j).symm)

/-- `b_sub_a` (1277), `speed = Λ`, `ℓ = juncLen ε (turn C j)` (504), `curveMap_b` (1661) -/
theorem ua_length_determined (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ) (hj : j < C.k) :
    (Round C D ε h).speed * ((Round C D ε h).b j - (Round C D ε h).a j) =
        CornerRounding.juncLen ε (principalTurn C.P j) ∧
    (Round C D ε h).Lε.γ ((Round C D ε h).b j) = C.P j + ε • CornerRounding.vDir C j := by
  constructor
  · show CornerRounding.Λ C ε * (CornerRounding.b C ε j - CornerRounding.a C ε j) = _
    rw [CornerRounding.b_sub_a, mul_div_cancel₀ _ (CornerRounding.Λ_pos h).ne']
    rfl
  · show CornerRounding.curveMap C ε (CornerRounding.b C ε j) = _
    rw [CornerRounding.curveMap_b h hj]
    rfl

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
  exact ⟨CornerRounding.normalize_deriv_curveMap h t,
    fun _ hj ht => CornerRounding.Θ_on_junction h hj ht⟩

/-- (U-B1 helper) a nonempty open interval is not covered by a countable set (Lebesgue measure:
a countable set is null, `Set.Countable.measure_zero`, while `volume (Ioo α β) = β − α > 0`) -/
theorem ub1_exists_notMem_of_countable {S : Set ℝ} (hS : S.Countable) {α β : ℝ} (hαβ : α < β) :
    ∃ φ ∈ Set.Ioo α β, φ ∉ S := by
  have h0 : MeasureTheory.volume (Set.Ioo α β \ S) ≠ 0 := by
    rw [MeasureTheory.measure_sdiff_null (hS.measure_zero _), Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hαβ)).ne'
  obtain ⟨φ, hφ⟩ := MeasureTheory.nonempty_of_measure_ne_zero h0
  exact ⟨φ, hφ.1, hφ.2⟩

/-- (U-B1 helper) every principal turn is `> −π`: `principalAngle` is a `Complex.arg`, whose range
is `(−π, π]` (no regularity or admissibility needed) -/
theorem ub1_neg_pi_lt_turn (C : PolyComp) (j : ZMod C.k) : -Real.pi < CornerRounding.turn C j :=
  Complex.neg_pi_lt_arg _

/-- (U-B1) an argument `φ` with `θu j ≢ φ (mod π)` for all `j` and, for a negative junction, no level
`φ + nπ` in its closed swept arc `[θu j + ϑ_j, θu j]` (the complement of the forbidden set in a period
is an open interval of length `π − |ϑ₋| > 0` minus finitely many points, `turn_bounds` 1155) -/
theorem ub_exists_direction (C : PolyComp) (hturn : ∀ i, principalTurn C.P i ≠ 0)
    (hpos : AllPosOrOneNeg C.P) :
    ∃ φ : ℝ, (∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ φ + n * Real.pi) ∧
      ∀ j, j < C.k → CornerRounding.turn C j < 0 →
        ∀ n : ℤ, φ + n * Real.pi ∉
          Set.Icc (CornerRounding.θu C j + CornerRounding.turn C j) (CornerRounding.θu C j) := by
  -- the forbidden set of the first clause, `{θu j − nπ ∣ j ∈ ℕ, n ∈ ℤ}`, is countable (so neither
  -- `rot ∈ ℤ` nor the periodicity `θu (j + k) = θu j + 2π rot` is needed)
  set S : Set ℝ := Set.range fun p : ℕ × ℤ => CornerRounding.θu C p.1 - p.2 * Real.pi
  have hS : S.Countable := Set.countable_range _
  have key : ∀ φ, φ ∉ S → ∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ φ + n * Real.pi := by
    intro φ hφ j n heq
    exact hφ ⟨(j, n), by show CornerRounding.θu C j - n * Real.pi = φ; rw [heq]; ring⟩
  rcases hpos with hall | ⟨i, _, hother⟩
  · -- all turns positive: the second clause is vacuous
    obtain ⟨φ, -, hφ⟩ := ub1_exists_notMem_of_countable hS (zero_lt_one' ℝ)
    refine ⟨φ, key φ hφ, fun j _ hneg _ _ => ?_⟩
    exact absurd (hall j) (not_lt.mpr hneg.le)
  · -- one negative turn at `i`: choose `φ` in the open gap `(θu i, θu i + ϑ_i + π)` of length
    -- `π − |ϑ_i| > 0` between the closed swept arc `[θu i + ϑ_i, θu i]` and its next `π`-translate
    obtain ⟨φ, hφmem, hφ⟩ := ub1_exists_notMem_of_countable hS
      (show CornerRounding.θu C i.val <
          CornerRounding.θu C i.val + CornerRounding.turn C i.val + Real.pi by
        have := ub1_neg_pi_lt_turn C (i.val : ZMod C.k); linarith)
    refine ⟨φ, key φ hφ, fun j hj hneg n hmem => ?_⟩
    -- the only negative junction with `j < k` is `j = i.val`
    have hji : (j : ZMod C.k) = i := by
      by_contra hne
      exact absurd (hother _ hne) (not_lt.mpr hneg.le)
    have hj0 : i.val = j := by rw [← hji, ZMod.val_cast_of_lt hj]
    rw [hj0] at hφmem
    rcases le_or_gt 0 n with hn | hn
    · -- `n ≥ 0`: `φ + nπ ≥ φ > θu j`
      have : (0 : ℝ) ≤ n * Real.pi := mul_nonneg (by exact_mod_cast hn) Real.pi_pos.le
      linarith [hmem.2, hφmem.1]
    · -- `n ≤ −1`: `φ + nπ ≤ φ − π < θu j + ϑ_j`
      have hn1 : n ≤ -1 := by omega
      have hn1' : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
      have : (n : ℝ) * Real.pi ≤ -Real.pi := by nlinarith [Real.pi_pos]
      linarith [hmem.1, hφmem.2]

section ub2

open Set CornerRounding

/-- (U-B2 helper) `dirOf α = dirOf β` iff the angles differ by an integer multiple of `2π` -/
theorem ub2_dirOf_eq_iff (α β : ℝ) :
    dirOf α = dirOf β ↔ ∃ n : ℤ, α = β + n * (2 * Real.pi) := by
  constructor
  · intro he
    have hc : Real.cos α = Real.cos β := congrArg Prod.fst he
    have hs : Real.sin α = Real.sin β := congrArg Prod.snd he
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hc hs)
    exact ⟨k, by linarith⟩
  · rintro ⟨n, rfl⟩
    unfold dirOf
    rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- (U-B2 helper) a value off every level `φ + mπ` is off every level `φ + 2πn` (`m = 2n`) -/
theorem ub2_level_ne {x φ : ℝ} (hx : ∀ m : ℤ, x ≠ φ + m * Real.pi) (n : ℤ) :
    x ≠ φ + n * (2 * Real.pi) := by
  intro he
  apply hx (2 * n)
  rw [he]; push_cast; ring

/-- (U-B2 helper, pure real) if the closed interval `[u, v]` contains no level `φ + 2πn` then the
floors of `(u − φ)/2π` and `(v − φ)/2π` agree -/
theorem ub2_floor_eq_of_no_level {u v φ : ℝ} (huv : u ≤ v)
    (hno : ∀ n : ℤ, φ + n * (2 * Real.pi) ∉ Icc u v) :
    ⌊(v - φ) / (2 * Real.pi)⌋ = ⌊(u - φ) / (2 * Real.pi)⌋ := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  refine le_antisymm ?_ (Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) h2π.le))
  by_contra hlt
  have hlt' := not_le.mp hlt
  apply hno ⌊(v - φ) / (2 * Real.pi)⌋
  constructor
  · have h1 := Int.floor_lt.mp hlt'
    rw [div_lt_iff₀ h2π] at h1
    linarith
  · have h1 := Int.floor_le ((v - φ) / (2 * Real.pi))
    rw [le_div_iff₀ h2π] at h1
    linarith

/-- (U-B2 helper, pure real) level counting for a continuous strictly increasing function on
`[a, b]` whose end value is not a level: the parameters `t ∈ (a, b)` with `g t ∈ φ + 2πℤ` form a
finite set of cardinality `⌊(g b − φ)/2π⌋ − ⌊(g a − φ)/2π⌋` (each level of `(g a, g b)` is attained
exactly once: intermediate value theorem and injectivity). -/
theorem ub2_levelCount_strictMonoOn {g : ℝ → ℝ} {a b φ : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) (hmono : StrictMonoOn g (Icc a b))
    (hb : ∀ n : ℤ, g b ≠ φ + n * (2 * Real.pi)) :
    {t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)}.Finite ∧
    ({t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)}.ncard : ℤ) =
      ⌊(g b - φ) / (2 * Real.pi)⌋ - ⌊(g a - φ) / (2 * Real.pi)⌋ := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlev_inj : Function.Injective (fun n : ℤ => φ + n * (2 * Real.pi)) := by
    intro m n hmn
    have h1 : (m : ℝ) * (2 * Real.pi) = n * (2 * Real.pi) := add_left_cancel hmn
    exact_mod_cast mul_right_cancel₀ h2π.ne' h1
  have hlt_iff : ∀ n : ℤ, g a < φ + n * (2 * Real.pi) ↔ ⌊(g a - φ) / (2 * Real.pi)⌋ < n := by
    intro n
    rw [Int.floor_lt, div_lt_iff₀ h2π]
    constructor <;> intro h <;> linarith
  have hle_iff : ∀ n : ℤ, φ + n * (2 * Real.pi) ≤ g b ↔ n ≤ ⌊(g b - φ) / (2 * Real.pi)⌋ := by
    intro n
    rw [Int.le_floor, le_div_iff₀ h2π]
    constructor <;> intro h <;> linarith
  have hSsub : {t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)} ⊆ Icc a b :=
    fun t ht => Ioo_subset_Icc_self ht.1
  have hinj : InjOn g {t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)} :=
    hmono.injOn.mono hSsub
  have himage : g '' {t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)} =
      (fun n : ℤ => φ + n * (2 * Real.pi)) ''
        (Finset.Ioc ⌊(g a - φ) / (2 * Real.pi)⌋ ⌊(g b - φ) / (2 * Real.pi)⌋ : Set ℤ) := by
    ext v
    constructor
    · rintro ⟨t, ⟨ht, n, hn⟩, rfl⟩
      refine ⟨n, ?_, hn.symm⟩
      rw [Finset.mem_coe, Finset.mem_Ioc, ← hlt_iff, ← hle_iff]
      have h1 : g a < g t := hmono ⟨le_rfl, hab.le⟩ (Ioo_subset_Icc_self ht) ht.1
      have h2 : g t < g b := hmono (Ioo_subset_Icc_self ht) ⟨hab.le, le_rfl⟩ ht.2
      rw [hn] at h1 h2
      exact ⟨h1, h2.le⟩
    · rintro ⟨n, hn, rfl⟩
      rw [Finset.mem_coe, Finset.mem_Ioc, ← hlt_iff, ← hle_iff] at hn
      have hn2 : φ + n * (2 * Real.pi) < g b := lt_of_le_of_ne hn.2 (fun he => hb n he.symm)
      obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hab.le hg ⟨hn.1.le, hn.2⟩
      refine ⟨t, ⟨⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, n, hgt⟩, hgt⟩
      · rintro rfl; exact hn.1.ne hgt
      · rintro rfl; exact hn2.ne' hgt
  have hfin_img : (g '' {t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)}).Finite := by
    rw [himage]; exact (Finset.finite_toSet _).image _
  have hfin := Set.Finite.of_finite_image hfin_img hinj
  refine ⟨hfin, ?_⟩
  have hcard : {t | t ∈ Ioo a b ∧ ∃ n : ℤ, g t = φ + n * (2 * Real.pi)}.ncard =
      (⌊(g b - φ) / (2 * Real.pi)⌋ - ⌊(g a - φ) / (2 * Real.pi)⌋).toNat := by
    rw [← hinj.ncard_image, himage, Set.ncard_image_of_injective _ hlev_inj, Set.ncard_coe_finset,
      Int.card_Ioc]
  rw [hcard, Int.toNat_of_nonneg]
  have hxy : (g a - φ) / (2 * Real.pi) ≤ (g b - φ) / (2 * Real.pi) := by
    have : g a < g b := hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
    exact div_le_div_of_nonneg_right (by linarith) h2π.le
  linarith [Int.floor_le_floor hxy]

variable {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ}

/-- (U-B2 helper) every parameter of `[a 0, a m)` lies in some `[a j, a (j+1))` with `j < m` -/
theorem ub2_locate (m : ℕ) {t : ℝ} (ht : t ∈ Ico (a C ε 0) (a C ε m)) :
    ∃ j, j < m ∧ t ∈ Ico (a C ε j) (a C ε (j + 1)) := by
  induction m with
  | zero => exact absurd (ht.1.trans_lt ht.2) (lt_irrefl _)
  | succ m ih =>
    rcases lt_or_ge t (a C ε m) with hlt | hge
    · obtain ⟨j, hj, hjt⟩ := ih ⟨ht.1, hlt⟩
      exact ⟨j, by omega, hjt⟩
    · exact ⟨m, by omega, hge, ht.2⟩

/-- (U-B2 helper) a level `φ + 2πn` of `Θ` met in `[a j, a (j+1))` is met in the open junction
`(a j, b j)`, by the junction lift `liftAt j` (`hφ`: `θu j`, `θu (j+1)` are not levels, so neither
the junction start `liftAt_a` nor the straight part `Θ_on_straight` carries one) -/
theorem ub2_level_in_junction (h : Admissible C D ε) {φ : ℝ}
    (hφ : ∀ (j : ℕ) (n : ℤ), θu C j ≠ φ + n * Real.pi) {j : ℕ} (hj : j < C.k) {t : ℝ}
    (ht : t ∈ Ico (a C ε j) (a C ε (j + 1))) {n : ℤ}
    (hn : Θ C ε t = φ + n * (2 * Real.pi)) :
    t ∈ Ioo (a C ε j) (b C ε j) ∧ liftAt C ε j t = φ + n * (2 * Real.pi) := by
  rcases lt_or_ge t (b C ε j) with hlt | hge
  · have hΘ := Θ_on_junction h hj ⟨ht.1, hlt.le⟩
    refine ⟨⟨lt_of_le_of_ne ht.1 ?_, hlt⟩, hΘ.symm.trans hn⟩
    rintro rfl
    rw [hΘ, liftAt_a] at hn
    exact ub2_level_ne (hφ j) n hn
  · exfalso
    rw [Θ_on_straight h hj ⟨hge, ht.2.le⟩] at hn
    exact ub2_level_ne (hφ (j + 1)) n hn

/-- (U-B2 helper) a level met inside an open junction forces a positive turn there: in a negative
junction the lift stays in the closed swept arc `[θu j + ϑ_j, θu j]` (`liftAt_strictAntiOn`), which
`harc` keeps free of levels -/
theorem ub2_turn_pos_of_level (h : Admissible C D ε) {φ : ℝ}
    (harc : ∀ j, j < C.k → CornerRounding.turn C j < 0 →
      ∀ n : ℤ, φ + n * Real.pi ∉ Icc (θu C j + CornerRounding.turn C j) (θu C j))
    {j : ℕ} (hj : j < C.k) {t : ℝ} (ht : t ∈ Ioo (a C ε j) (b C ε j)) {n : ℤ}
    (hn : liftAt C ε j t = φ + n * (2 * Real.pi)) : 0 < CornerRounding.turn C j := by
  rcases lt_or_gt_of_ne (turn_bounds h j).1 with hneg | hpos
  · exfalso
    have hanti := (liftAt_strictAntiOn h hneg).antitoneOn
    have hIcc : t ∈ Icc (a C ε j) (b C ε j) := Ioo_subset_Icc_self ht
    have h1 : liftAt C ε j t ≤ liftAt C ε j (a C ε j) :=
      hanti ⟨le_rfl, (a_lt_b h j).le⟩ hIcc ht.1.le
    have h2 : liftAt C ε j (b C ε j) ≤ liftAt C ε j t :=
      hanti hIcc ⟨(a_lt_b h j).le, le_rfl⟩ ht.2.le
    rw [liftAt_a, hn] at h1
    rw [liftAt_b h, hn] at h2
    apply harc j hj hneg (2 * n)
    push_cast
    constructor <;> linarith
  · exact hpos

/-- (U-B2 helper) in a positive junction the angular derivative of the junction lift is positive at
every interior parameter (`G3_hasDerivAt_liftAt`, `deriv_smoothTransition_pos`) -/
theorem ub2_deriv_liftAt_pos (h : Admissible C D ε) {j : ℕ} (hpos : 0 < CornerRounding.turn C j) {t : ℝ}
    (ht : t ∈ Ioo (a C ε j) (b C ε j)) : 0 < deriv (liftAt C ε j) t := by
  rw [(G3_hasDerivAt_liftAt j t).deriv]
  obtain ⟨hs0, hs1⟩ := G3_junction_arg_mem_Ioo h j ht
  have h1 := deriv_smoothTransition_pos hs0 hs1
  have h2 : 0 < 1 * Λ C ε / ℓ C ε j := by
    rw [one_mul]; exact div_pos (Λ_pos h) (ℓ_pos h j)
  exact mul_pos hpos (mul_pos h1 h2)

/-- (U-B2 helper) the levels of `Θ` met in `[a j, a (j+1))`: a finite set of cardinality
`⌊x_{j+1}⌋ − ⌊x_j⌋`, `x_j := (θu j − φ)/2π` (positive junction: `ub2_levelCount_strictMonoOn` on the
junction lift; negative junction: no level at all, and equal floors by `harc`) -/
theorem ub2_junction_count (h : Admissible C D ε) {φ : ℝ}
    (hφ : ∀ (j : ℕ) (n : ℤ), θu C j ≠ φ + n * Real.pi)
    (harc : ∀ j, j < C.k → CornerRounding.turn C j < 0 →
      ∀ n : ℤ, φ + n * Real.pi ∉ Icc (θu C j + CornerRounding.turn C j) (θu C j))
    {j : ℕ} (hj : j < C.k) :
    {t | t ∈ Ico (a C ε j) (a C ε (j + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)}.Finite ∧
    ({t | t ∈ Ico (a C ε j) (a C ε (j + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)}.ncard : ℤ) =
      ⌊(θu C (j + 1) - φ) / (2 * Real.pi)⌋ - ⌊(θu C j - φ) / (2 * Real.pi)⌋ := by
  rcases lt_or_gt_of_ne (turn_bounds h j).1 with hneg | hpos
  · have hempty :
        {t | t ∈ Ico (a C ε j) (a C ε (j + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
      intro ht n hn
      obtain ⟨hIoo, hl⟩ := ub2_level_in_junction h hφ hj ht hn
      exact absurd (ub2_turn_pos_of_level h harc hj hIoo hl) (not_lt.mpr hneg.le)
    rw [hempty, Set.ncard_empty]
    refine ⟨Set.finite_empty, ?_⟩
    have hfl := ub2_floor_eq_of_no_level (u := θu C j + CornerRounding.turn C j) (v := θu C j) (φ := φ)
      (by linarith) (fun n => ?_)
    · show (((0 : ℕ) : ℤ)) = ⌊(θu C j + CornerRounding.turn C j - φ) / (2 * Real.pi)⌋ - ⌊(θu C j - φ) / (2 * Real.pi)⌋
      rw [hfl]; simp
    · have := harc j hj hneg (2 * n)
      push_cast at this
      convert this using 3
      ring
  · have hseteq :
        {t | t ∈ Ico (a C ε j) (a C ε (j + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} =
        {t | t ∈ Ioo (a C ε j) (b C ε j) ∧ ∃ n : ℤ, liftAt C ε j t = φ + n * (2 * Real.pi)} := by
      ext t
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨ht, n, hn⟩
        obtain ⟨hIoo, hl⟩ := ub2_level_in_junction h hφ hj ht hn
        exact ⟨hIoo, n, hl⟩
      · rintro ⟨ht, n, hn⟩
        refine ⟨⟨ht.1.le, ht.2.trans (b_lt_a h hj)⟩, n, ?_⟩
        rw [Θ_on_junction h hj (Ioo_subset_Icc_self ht)]
        exact hn
    rw [hseteq]
    have hcount := ub2_levelCount_strictMonoOn (g := liftAt C ε j) (φ := φ) (a_lt_b h j)
      (liftAt_smooth j).continuous.continuousOn (liftAt_strictMonoOn h hpos)
      (by rw [liftAt_b h]; exact ub2_level_ne (hφ (j + 1)))
    rw [liftAt_a, liftAt_b h] at hcount
    exact hcount

/-- (U-B2 helper) the cumulative count on `[a 0, a m)`, `m ≤ k`: `⌊x_m⌋ − ⌊x_0⌋` (induction on `m`,
`ub2_junction_count` for the new piece `[a m, a (m+1))`, disjoint union) -/
theorem ub2_cumulative_count (h : Admissible C D ε) {φ : ℝ}
    (hφ : ∀ (j : ℕ) (n : ℤ), θu C j ≠ φ + n * Real.pi)
    (harc : ∀ j, j < C.k → CornerRounding.turn C j < 0 →
      ∀ n : ℤ, φ + n * Real.pi ∉ Icc (θu C j + CornerRounding.turn C j) (θu C j))
    {m : ℕ} (hm : m ≤ C.k) :
    {t | t ∈ Ico (a C ε 0) (a C ε m) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)}.Finite ∧
    ({t | t ∈ Ico (a C ε 0) (a C ε m) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)}.ncard : ℤ) =
      ⌊(θu C m - φ) / (2 * Real.pi)⌋ - ⌊(θu C 0 - φ) / (2 * Real.pi)⌋ := by
  induction m with
  | zero =>
    have hempty :
        {t | t ∈ Ico (a C ε 0) (a C ε 0) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} = ∅ := by
      ext t
      simp
    rw [hempty]
    simp
  | succ m ih =>
    obtain ⟨hfin, hcard⟩ := ih (by omega)
    obtain ⟨hfinJ, hcardJ⟩ := ub2_junction_count h hφ harc (show m < C.k by omega)
    have hunion :
        {t | t ∈ Ico (a C ε 0) (a C ε (m + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} =
        {t | t ∈ Ico (a C ε 0) (a C ε m) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} ∪
        {t | t ∈ Ico (a C ε m) (a C ε (m + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} := by
      ext t
      simp only [mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨ht, hP⟩
        rcases lt_or_ge t (a C ε m) with hlt | hge
        · exact Or.inl ⟨⟨ht.1, hlt⟩, hP⟩
        · exact Or.inr ⟨⟨hge, ht.2⟩, hP⟩
      · rintro (⟨ht, hP⟩ | ⟨ht, hP⟩)
        · exact ⟨⟨ht.1, ht.2.trans_le ((G2_a_strictMono h).monotone (Nat.le_succ m))⟩, hP⟩
        · exact ⟨⟨((G2_a_strictMono h).monotone (Nat.zero_le m)).trans ht.1, ht.2⟩, hP⟩
    have hdisj : Disjoint
        {t | t ∈ Ico (a C ε 0) (a C ε m) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)}
        {t | t ∈ Ico (a C ε m) (a C ε (m + 1)) ∧ ∃ n : ℤ, Θ C ε t = φ + n * (2 * Real.pi)} := by
      rw [Set.disjoint_left]
      rintro t ⟨ht, -⟩ ⟨ht', -⟩
      exact absurd ht.2 (not_lt.mpr ht'.1)
    rw [hunion]
    refine ⟨hfin.union hfinJ, ?_⟩
    rw [Set.ncard_union_eq hdisj hfin hfinJ]
    push_cast
    rw [hcard, hcardJ]
    ring

end ub2

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
  have _ := hrot -- not needed: the count is the (nonnegative) telescoped floor difference
  have hT : ∀ t, (Round C D ε h).T t = CornerRounding.dirOf (CornerRounding.Θ C ε t) :=
    fun t => CornerRounding.normalize_deriv_curveMap h t
  have hset : tangencySet (Round C D ε h) (CornerRounding.dirOf φ) =
      {t | t ∈ Set.Ico (CornerRounding.a C ε 0) (CornerRounding.a C ε C.k) ∧
        ∃ n : ℤ, CornerRounding.Θ C ε t = φ + n * (2 * Real.pi)} := by
    ext t
    simp only [tangencySet, Set.mem_ofPred_eq, CornerRounding.a_zero, CornerRounding.a_last h]
    rw [hT, ub2_dirOf_eq_iff]
  obtain ⟨hfin, hcard⟩ := ub2_cumulative_count h hφ harc (le_refl C.k)
  refine ⟨hset ▸ hfin, ?_, ?_⟩
  · rw [hset]
    obtain ⟨r, hr⟩ := rotationNumber_integer D.regular
    rw [CornerRounding.θu_last, hr] at hcard
    have hx : (CornerRounding.θu C 0 + 2 * Real.pi * (r : ℝ) - φ) / (2 * Real.pi) =
        (CornerRounding.θu C 0 - φ) / (2 * Real.pi) + r := by
      field_simp
      ring
    rw [hx, Int.floor_add_intCast] at hcard
    have hcard' : ({t | t ∈ Set.Ico (CornerRounding.a C ε 0) (CornerRounding.a C ε C.k) ∧
        ∃ n : ℤ, CornerRounding.Θ C ε t = φ + n * (2 * Real.pi)}.ncard : ℤ) = r := by linarith
    rw [hr]
    exact_mod_cast hcard'
  · intro t ht
    rw [hset] at ht
    obtain ⟨ht01, n, hn⟩ := ht
    obtain ⟨j, hj, hjt⟩ := ub2_locate C.k ht01
    obtain ⟨hIoo, hl⟩ := ub2_level_in_junction h hφ hj hjt hn
    have hpos := ub2_turn_pos_of_level h harc hj hIoo hl
    exact ⟨j, hj, hIoo, ub2_deriv_liftAt_pos h hpos hIoo⟩


/-- (U-B3 helper) `dirOf (α + π) = −dirOf α` -/
theorem ub3_dirOf_add_pi (α : ℝ) :
    CornerRounding.dirOf (α + Real.pi) = -CornerRounding.dirOf α := by
  unfold CornerRounding.dirOf
  rw [Real.cos_add_pi, Real.sin_add_pi]
  rfl

/-- (U-B3 helper) `dirOf (φ + nπ) = ±dirOf φ` (`n` even / odd) -/
theorem ub3_dirOf_add_int_mul_pi (φ : ℝ) (n : ℤ) :
    CornerRounding.dirOf (φ + n * Real.pi) = CornerRounding.dirOf φ ∨
    CornerRounding.dirOf (φ + n * Real.pi) = -CornerRounding.dirOf φ := by
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [ub2_dirOf_eq_iff]
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  · right
    rw [← ub3_dirOf_add_pi, ub2_dirOf_eq_iff]
    exact ⟨m, by rw [hm]; push_cast; ring⟩

/-- (U-B3 helper) for an admissible direction `u` and any angle `ψ` with `dirOf ψ = ±u`, no `θu j`
lies on a level `ψ + nπ` (`dirOf (θu j) = u_j` is an edge direction, `dirOf_θu`) -/
theorem ub3_levels_of_admissible (C : PolyComp) (hreg : Regular C.P) {u : Plane}
    (hu : AdmissibleDirection C u) {ψ : ℝ}
    (hψ : CornerRounding.dirOf ψ = u ∨ CornerRounding.dirOf ψ = -u) :
    ∀ (j : ℕ) (n : ℤ), CornerRounding.θu C j ≠ ψ + n * Real.pi := by
  intro j n heq
  have h1 : CornerRounding.dirOf (CornerRounding.θu C j) =
      SM.normalize (edge C.P ((j : ZMod C.k) - 1)) := by
    rw [CornerRounding.dirOf_θu hreg]; rfl
  have h2 := ub3_dirOf_add_int_mul_pi ψ n
  rw [← heq, h1] at h2
  obtain ⟨hne1, hne2⟩ := hu.2.1 ((j : ZMod C.k) - 1)
  rcases hψ with hψ | hψ <;> rcases h2 with h2 | h2
  · exact hne1 (h2.trans hψ)
  · exact hne2 (h2.trans (by rw [hψ]))
  · exact hne2 (h2.trans hψ)
  · exact hne1 (h2.trans (by rw [hψ, neg_neg]))

/-- (U-B3 helper) for an admissible direction `u` and any angle `ψ` with `dirOf ψ = ±u`, the
closed swept arc `[θu j + ϑ_j, θu j]` of a negative junction carries no level `ψ + nπ`
(`s := (ψ + nπ − θu j)/ϑ_j ∈ [0,1]` would violate the arc clause of `AdmissibleDirection`) -/
theorem ub3_arc_of_admissible (C : PolyComp) (hreg : Regular C.P) {u : Plane}
    (hu : AdmissibleDirection C u) {ψ : ℝ}
    (hψ : CornerRounding.dirOf ψ = u ∨ CornerRounding.dirOf ψ = -u) :
    ∀ j, j < C.k → CornerRounding.turn C j < 0 →
      ∀ n : ℤ, ψ + n * Real.pi ∉
        Set.Icc (CornerRounding.θu C j + CornerRounding.turn C j) (CornerRounding.θu C j) := by
  intro j _ hneg n hmem
  have hpt : principalTurn C.P (j : ZMod C.k) = CornerRounding.turn C j := rfl
  have hs0 : 0 ≤ (ψ + n * Real.pi - CornerRounding.θu C j) / CornerRounding.turn C j :=
    div_nonneg_of_nonpos (by linarith [hmem.2]) hneg.le
  have hs1 : (ψ + n * Real.pi - CornerRounding.θu C j) / CornerRounding.turn C j ≤ 1 := by
    rw [div_le_one_of_neg hneg]; linarith [hmem.1]
  have hsx : CornerRounding.θu C j +
      (ψ + n * Real.pi - CornerRounding.θu C j) / CornerRounding.turn C j * CornerRounding.turn C j =
      ψ + n * Real.pi := by
    rw [div_mul_cancel₀ _ hneg.ne]; ring
  obtain ⟨hne1, hne2⟩ := hu.2.2 (j : ZMod C.k) (by rw [hpt]; exact hneg)
    ((ψ + n * Real.pi - CornerRounding.θu C j) / CornerRounding.turn C j) ⟨hs0, hs1⟩
  rw [hpt] at hne1 hne2
  have hdir : CornerRounding.dirOf ((planeComplex (CornerRounding.uDir C (j : ZMod C.k))).arg) =
      CornerRounding.dirOf (CornerRounding.θu C j) := by
    rw [ua_dirOf_arg_uDir C hreg, CornerRounding.dirOf_θu hreg]
  obtain ⟨m, hm⟩ := (ub2_dirOf_eq_iff _ _).mp hdir
  have hdir2 : CornerRounding.dirOf ((planeComplex (CornerRounding.uDir C (j : ZMod C.k))).arg +
      (ψ + n * Real.pi - CornerRounding.θu C j) / CornerRounding.turn C j * CornerRounding.turn C j) =
      CornerRounding.dirOf (ψ + n * Real.pi) := by
    rw [ub2_dirOf_eq_iff]
    exact ⟨m, by rw [hm]; linarith [hsx]⟩
  have h2 := ub3_dirOf_add_int_mul_pi ψ n
  rw [← hdir2] at h2
  rcases hψ with hψ | hψ <;> rcases h2 with h2 | h2
  · exact hne1 (h2.trans hψ)
  · exact hne2 (h2.trans (by rw [hψ]))
  · exact hne2 (h2.trans hψ)
  · exact hne1 (h2.trans (by rw [hψ, neg_neg]))

/-- (U-B3 helper) in the normalised orientation (all turns positive, or exactly one negative) the
rotation number is positive: `uniform_rotation` (i)/(iii) through `principalTurn_sign` -/
theorem ub3_rotationNumber_pos (C : PolyComp) (hreg : Regular C.P)
    (hturn : ∀ i, principalTurn C.P i ≠ 0) (hpos : AllPosOrOneNeg C.P) :
    0 < rotationNumber C.P := by
  have hτ : ∀ i : ZMod C.k, SM.turn C.P i ≠ 0 := by
    intro i he
    apply hturn i
    have := principalTurn_sign hreg i
    rw [he] at this
    exact sign_eq_zero_iff.mp this
  have hur := uniform_rotation C.hk C.P hreg hτ
  have h1 : (1 : ℝ) ≤ rotationNumber C.P := by
    rcases hpos with hall | ⟨a, ha, hother⟩
    · apply hur.1
      intro i
      rw [← principalTurn_sign hreg i]
      exact sign_pos (hall i)
    · apply hur.2.2.1
      refine ⟨a, ?_, fun i hi => ?_⟩
      · rw [← principalTurn_sign hreg a]; exact sign_neg ha
      · rw [← principalTurn_sign hreg i]; exact sign_pos (hother i hi)
  linarith

/-- (U-B3, library leaf) for every admissible direction and every admissible `ε` (the printed proof,
with `ε₁ = ε₀(L)`): from `ub_globalLift`, `ub_levelCount` at `φ` and at `φ + π` (`dirOf (φ + π) = −dirOf φ`),
`rot ≥ 1` in both normalised cases (`uniform_rotation` via `principalTurn_sign`), `|rot| = rot`. -/
theorem ub_tangencyCount_of_admissible (C : PolyComp) (D : PolygonDiagram C)
    (hturn : ∀ i, principalTurn C.P i ≠ 0) (hpos : AllPosOrOneNeg C.P) (u : Plane)
    (hu : AdmissibleDirection C u) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    TangencyCount (Round C D ε h) u |rotationNumber C.P| ∧
    TangencyCount (Round C D ε h) (-u) |rotationNumber C.P| := by
  have hreg : Regular C.P := D.regular
  -- `φ := arg u`, `dirOf φ = u` (polar form `G1_smul_dirOf_arg` with `|u| = 1`)
  have hdirφ : CornerRounding.dirOf (planeComplex u).arg = u := by
    have := CornerRounding.G1_smul_dirOf_arg u
    rwa [hu.1, one_smul] at this
  have hdirφπ : CornerRounding.dirOf ((planeComplex u).arg + Real.pi) = -u := by
    rw [ub3_dirOf_add_pi, hdirφ]
  -- `rot ≥ 1 > 0` in the normalised orientation, so `|rot| = rot`
  have hrot : 0 < rotationNumber C.P := ub3_rotationNumber_pos C hreg hturn hpos
  rw [abs_of_pos hrot]
  constructor
  · -- `ub_levelCount` at `φ`
    have := ub_levelCount C D ε h (planeComplex u).arg
      (ub3_levels_of_admissible C hreg hu (Or.inl hdirφ))
      (ub3_arc_of_admissible C hreg hu (Or.inl hdirφ)) hrot
    rwa [hdirφ] at this
  · -- `ub_levelCount` at `φ + π` (`dirOf (φ + π) = −u`)
    have := ub_levelCount C D ε h ((planeComplex u).arg + Real.pi)
      (ub3_levels_of_admissible C hreg hu (Or.inr hdirφπ))
      (ub3_arc_of_admissible C hreg hu (Or.inr hdirφπ)) hrot
    rwa [hdirφπ] at this

/-- (U-B3, library leaf) "Such u exists" (sm-3:4374-4376): `u := dirOf φ` from `ub_exists_direction`
(`dirOf (θu j) = uDir j`, 1207). -/
theorem ub_exists_admissibleDirection (C : PolyComp) (hreg : Regular C.P)
    (hturn : ∀ i, principalTurn C.P i ≠ 0) (hpos : AllPosOrOneNeg C.P) :
    ∃ u : Plane, AdmissibleDirection C u := by
  -- (assembler, wave 1) `u := dirOf φ` for the `φ` of `ub_exists_direction`; `dirOf (θu j) = uDir j`
  -- (`dirOf_θu`), `dirOf α = dirOf β ↔ α ≡ β (mod 2π)` (`ub2_dirOf_eq_iff`), `−dirOf φ = dirOf (φ + π)`
  obtain ⟨φ, hφ, harc⟩ := ub_exists_direction C hturn hpos
  have hneg : -CornerRounding.dirOf φ = CornerRounding.dirOf (φ + Real.pi) := by
    unfold CornerRounding.dirOf
    rw [Real.cos_add_pi, Real.sin_add_pi]
    rfl
  -- no point of the lattice `θu C m + 2πℤ` has direction `± dirOf φ`
  have hlev : ∀ (m : ℕ) (x : ℝ), (∃ n : ℤ, x = CornerRounding.θu C m + n * (2 * Real.pi)) →
      CornerRounding.dirOf x ≠ CornerRounding.dirOf φ ∧
      CornerRounding.dirOf x ≠ -CornerRounding.dirOf φ := by
    rintro m x ⟨n, rfl⟩
    constructor
    · intro he
      obtain ⟨n', hn'⟩ := (ub2_dirOf_eq_iff _ _).mp he
      apply hφ m (2 * (n' - n))
      push_cast
      linarith
    · intro he
      rw [hneg] at he
      obtain ⟨n', hn'⟩ := (ub2_dirOf_eq_iff _ _).mp he
      apply hφ m (2 * (n' - n) + 1)
      push_cast
      linarith
  refine ⟨CornerRounding.dirOf φ, CornerRounding.dirOf_unit φ, fun i => ?_, fun j hj s hs => ?_⟩
  · -- edge directions: `normalize (edge C.P i) = uDir C (i + 1) = dirOf (θu C (i + 1).val)`
    have h1 : CornerRounding.dirOf (CornerRounding.θu C (i + 1).val) = SM.normalize (edge C.P i) := by
      rw [CornerRounding.dirOf_θu hreg, ZMod.natCast_zmod_val]
      show SM.normalize (edge C.P (i + 1 - 1)) = _
      rw [add_sub_cancel_right]
    rw [← h1]
    exact hlev (i + 1).val _ ⟨0, by simp⟩
  · -- the closed swept arc of a negative turn: `θu + s ϑ ∈ [θu + ϑ, θu]`, kept level-free by `harc`
    have hjv : ((j.val : ℕ) : ZMod C.k) = j := ZMod.natCast_zmod_val j
    have hjlt : j.val < C.k := ZMod.val_lt j
    have ht : CornerRounding.turn C ((j.val : ℕ) : ZMod C.k) = principalTurn C.P j := by
      show principalTurn C.P ((j.val : ℕ) : ZMod C.k) = _
      rw [hjv]
    have hturnj : CornerRounding.turn C ((j.val : ℕ) : ZMod C.k) < 0 := by rw [ht]; exact hj
    have hdir : CornerRounding.dirOf (planeComplex (CornerRounding.uDir C j)).arg =
        CornerRounding.dirOf (CornerRounding.θu C j.val) := by
      rw [ua_dirOf_arg_uDir C hreg j, CornerRounding.dirOf_θu hreg, hjv]
    obtain ⟨m, hm⟩ := (ub2_dirOf_eq_iff _ _).mp hdir
    have hmem : CornerRounding.θu C j.val + s * principalTurn C.P j ∈
        Set.Icc (CornerRounding.θu C j.val + CornerRounding.turn C ((j.val : ℕ) : ZMod C.k))
          (CornerRounding.θu C j.val) := by
      rw [ht]
      constructor <;> nlinarith [hs.1, hs.2, hj]
    constructor
    · intro he
      obtain ⟨n, hn⟩ := (ub2_dirOf_eq_iff _ _).mp he
      apply harc j.val hjlt hturnj (2 * (n - m))
      have e : φ + ((2 * (n - m) : ℤ) : ℝ) * Real.pi =
          CornerRounding.θu C j.val + s * principalTurn C.P j := by
        push_cast
        linarith
      rw [e]
      exact hmem
    · intro he
      rw [hneg] at he
      obtain ⟨n, hn⟩ := (ub2_dirOf_eq_iff _ _).mp he
      apply harc j.val hjlt hturnj (2 * (n - m) + 1)
      have e : φ + ((2 * (n - m) + 1 : ℤ) : ℝ) * Real.pi =
          CornerRounding.θu C j.val + s * principalTurn C.P j := by
        push_cast
        linarith
      rw [e]
      exact hmem

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
  coeff : ∀ (f : R) (d k : ℤ), coeffAt d k (ι f) = (-1) ^ k.natAbs * coeffAt (-d) k f
  degAZ_eq : ∀ f : R, f ≠ 0 → degAZ (ι f) = -mindegAZ f
  ne_zero : ∀ f : R, f ≠ 0 → ι f ≠ 0

/-! #### Unit U-ι helpers (prefix `ui_`): `ι` on monomials, the coefficient law, the extreme
`a`-degree.  The sign of `(−z)^q` is `(−1)^q`, well defined for NEGATIVE `q` (the ring `R` has
`z⁻¹`); it is rendered `(-1) ^ q.natAbs`. -/

/-- the unit `(a⁻¹)^p (−z)^q` is the monomial `(−1)^q a^{−p} z^q` -/
theorem ui_unitPowers_iota (p q : ℤ) :
    ((R.aUnit⁻¹ ^ p * (-R.zUnit) ^ q : Rˣ) : R) =
      AddMonoidAlgebra.single (-p, q) ((-1) ^ q.natAbs) := by
  have h1 : (R.aUnit⁻¹ ^ p : Rˣ) = Laurent₂.monoUnit (-p, 0) := by
    rw [R.aUnit, Laurent₂.monoUnit_inv, Laurent₂.monoUnit_zpow]
    congr 1
    ext <;> simp
  have h2 : ((-R.zUnit) ^ q : Rˣ) = (-1) ^ q * Laurent₂.monoUnit (0, q) := by
    rw [neg_eq_neg_one_mul, mul_zpow, R.zUnit, Laurent₂.monoUnit_zpow]
    congr 2
    ext <;> simp
  rw [h1, h2]
  rcases Int.even_or_odd q with hq | hq
  · rw [hq.neg_one_zpow, one_mul, Laurent₂.monoUnit_mul, Laurent₂.val_monoUnit,
      Even.neg_one_pow (Int.natAbs_even.2 hq)]
    congr 1
    ext <;> simp
  · rw [hq.neg_one_zpow, neg_one_mul, mul_neg, Laurent₂.monoUnit_mul, Units.val_neg,
      Laurent₂.val_monoUnit, Odd.neg_one_pow (Int.natAbs_odd.2 hq), ← AddMonoidAlgebra.single_neg]
    congr 1
    ext <;> simp

/-- `ι (c a^p z^q) = (−1)^q c a^{−p} z^q` -/
theorem ui_iotaHom_single (p q c : ℤ) :
    iotaHom (AddMonoidAlgebra.single (p, q) c) =
      AddMonoidAlgebra.single (-p, q) (c * (-1) ^ q.natAbs) := by
  show AddMonoidAlgebra.lift ℤ R (ℤ × ℤ) (unitPowers (R.aUnit⁻¹) (-R.zUnit))
    (AddMonoidAlgebra.single (p, q) c) = _
  rw [AddMonoidAlgebra.lift_single, unitPowers_apply, ui_unitPowers_iota,
    AddMonoidAlgebra.smul_single']

theorem ui_coeffAt_smul (r : ℤ) (f : R) (d k : ℤ) : coeffAt d k (r • f) = r * coeffAt d k f := rfl

/-- the TRUE coefficient law `[a^d z^k] (ι f) = (−1)^k [a^{−d} z^k] f`, with `(−1)^k` read as
`(-1) ^ k.natAbs` so that it is right for negative `k` as well -/
theorem ui_coeffAt_iotaHom (f : R) (d k : ℤ) :
    coeffAt d k (iotaHom f) = (-1) ^ k.natAbs * coeffAt (-d) k f := by
  induction f using AddMonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨p, q⟩ := m
    rw [AddMonoidAlgebra.of_apply, toAdd_ofAdd, ui_iotaHom_single, coeffAt_single, coeffAt_single]
    by_cases h : p = -d ∧ q = k
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · have h1 : ¬ ((-p, q) = (d, k)) := by
        intro h'; apply h; simp only [Prod.mk.injEq] at h'; omega
      have h2 : ¬ ((p, q) = (-d, k)) := by
        intro h'; apply h; simp only [Prod.mk.injEq] at h'; omega
      simp [h1, h2]
  | add x y hx hy => rw [map_add, coeffAt_add, coeffAt_add, hx, hy, mul_add]
  | smul r x hx =>
    rw [map_zsmul, ui_coeffAt_smul, ui_coeffAt_smul, hx]; ring

/-- the `k.toNat` form of the law holds for `0 ≤ k` (there `k.natAbs = k.toNat`) -/
theorem ui_coeffAt_iotaHom_of_nonneg (f : R) (d k : ℤ) (hk : 0 ≤ k) :
    coeffAt d k (iotaHom f) = (-1) ^ k.toNat * coeffAt (-d) k f := by
  rw [ui_coeffAt_iotaHom, show k.natAbs = k.toNat by omega]

/-- REFUTATION of the `coeff` field of `MirrorSubstitutionData` AS STATED: `(-1) ^ k.toNat = 1`
for every negative `k`, but `ι z⁻¹ = −z⁻¹`, so at `f = z⁻¹`, `d = 0`, `k = −1` the two sides are
`−1` and `1`.  The field must read `(-1) ^ k.natAbs` (`ui_coeffAt_iotaHom`). -/
theorem ui_coeff_toNat_false :
    ¬ ∀ (f : R) (d k : ℤ), coeffAt d k (iotaHom f) = (-1) ^ k.toNat * coeffAt (-d) k f := by
  intro h
  have := h R.zInv 0 (-1)
  rw [R.zInv, ui_iotaHom_single, coeffAt_single, coeffAt_single,
    show ((-1 : ℤ)).toNat = 0 by decide] at this
  norm_num at this

/-- "the substitution negates every a-exponent and cannot cancel a nonzero extreme coefficient":
`max deg_a (ι f) = −min deg_a f` -/
theorem ui_degAZ_iotaHom (f : R) (hf : f ≠ 0) : degAZ (iotaHom f) = -mindegAZ f := by
  obtain ⟨⟨k, hk⟩, hb⟩ := mindegAZ_spec hf
  apply degAZ_eq_of_spec
  · refine ⟨k, ?_⟩
    rw [ui_coeffAt_iotaHom, neg_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hk
  · intro d' k' h
    rw [ui_coeffAt_iotaHom] at h
    have := hb _ _ (right_ne_zero_of_mul h)
    linarith

theorem ui_iotaHom_ne_zero (f : R) (hf : f ≠ 0) : iotaHom f ≠ 0 := by
  obtain ⟨⟨k, hk⟩, -⟩ := mindegAZ_spec hf
  intro h0
  have := ui_coeffAt_iotaHom f (-mindegAZ f) k
  rw [h0, coeffAt_zero, neg_neg] at this
  exact hk ((mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ (by norm_num)))

theorem ui_iotaHom_a : iotaHom R.a = R.aInv := by
  rw [R.a, ui_iotaHom_single]; simp [R.aInv]

theorem ui_iotaHom_aInv : iotaHom R.aInv = R.a := by
  rw [R.aInv, ui_iotaHom_single]; simp [R.a]

theorem ui_iotaHom_z : iotaHom R.z = -R.z := by
  rw [R.z, ui_iotaHom_single]; simp [AddMonoidAlgebra.single_neg]

theorem ui_iotaHom_zInv : iotaHom R.zInv = -R.zInv := by
  rw [R.zInv, ui_iotaHom_single]; simp [AddMonoidAlgebra.single_neg]

/-- `ι ∘ ι = id` (for U-EQ's "`ι` is applied once more") -/
theorem ui_iotaHom_iotaHom (f : R) : iotaHom (iotaHom f) = f := by
  apply ext_coeffAt
  intro d k
  rw [ui_coeffAt_iotaHom, ui_coeffAt_iotaHom, neg_neg, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul]
  simp

theorem ui_mirrorSubstitution : MirrorSubstitutionData iotaHom :=
  ⟨ui_iotaHom_a, ui_iotaHom_aInv, ui_iotaHom_z, ui_coeffAt_iotaHom, ui_degAZ_iotaHom, ui_iotaHom_ne_zero⟩

/-- (U-EQ helper) `D ↦ ι(P_{D̄})` satisfies the hypotheses of lp:coefficient-transport (`RCompetitor`,
CoefficientTransport.lean:23): planar isotopy and the three Reidemeister moves are carried by the
crossing switch (`usw_switchAllCarries.planar/ri/rii/riii`) and `P` is invariant under them
(`P_planar`, `P_reidemeister_*`, PolynomialBlock.lean:604-607), `ι` being a function; the crossing-free
circle is carried (`usw_switchAllCarries.circle`), `P_circle` (609) and `ι 1 = 1`; on a skein triple
`(D₊, D₋, D₀)` the switched triple is `(D̄₋, D̄₊, D̄₀)` (`usw_switchAllCarries.skein`), so `P_skein` (638)
reads `a P_{D̄₋} − a⁻¹ P_{D̄₊} = z P_{D̄₀}`; applying the ring hom `ι` (`ι_a = a⁻¹`, `ι_aInv = a`,
`ι_z = −z`) gives `a⁻¹ ι P_{D̄₋} − a ι P_{D̄₊} = −z ι P_{D̄₀}`, the campaign skein "multiplied by −1"
(sm-3:4540-4544). -/
theorem ueq_iota_switchAll_rcompetitor :
    RCompetitor (fun D : Diagram => iotaHom (P D.switchAll)) where
  planar := fun D D' h => congrArg iotaHom (P_planar (usw_switchAllCarries.planar D D' h))
  reidemeister_I := fun D D' h =>
    congrArg iotaHom (P_reidemeister_I (usw_switchAllCarries.ri D D' h))
  reidemeister_II := fun D D' h =>
    congrArg iotaHom (P_reidemeister_II (usw_switchAllCarries.rii D D' h))
  reidemeister_III := fun D D' h =>
    congrArg iotaHom (P_reidemeister_III (usw_switchAllCarries.riii D D' h))
  circle := fun D h => by
    show iotaHom (P D.switchAll) = 1
    rw [P_circle (usw_switchAllCarries.circle D h), map_one]
  skein := fun Dp Dm D0 h => by
    show R.a * iotaHom (P Dp.switchAll) - R.aInv * iotaHom (P Dm.switchAll) =
      R.z * iotaHom (P D0.switchAll)
    have h1 := congrArg iotaHom (P_skein (usw_switchAllCarries.skein Dp Dm D0 h))
    rw [map_sub, map_mul, map_mul, map_mul, ui_iotaHom_a, ui_iotaHom_aInv, ui_iotaHom_z] at h1
    linear_combination -h1

/-- (U-EQ) the mirror identity `P_{D̄}(a, z) = P_D(a⁻¹, −z)` (sm-3:4533-4551): `D ↦ ι(P_{D̄})` is an
`RCompetitor` (`usw_switchAllCarries` + lp:core + `ι` a ring hom, the skein "multiplied by −1"), so
`coefficient_transport` identifies it with `P` and `ι` is applied once more (`ι ∘ ι = id`). -/
theorem usw_P_switchAll (X : Diagram) : P X.switchAll = iotaHom (P X) := by
  -- (U-EQ) `coefficient_transport` gives `ι (P X̄) = P X`; apply `ι` once more and use `ι ∘ ι = id`
  exact (ui_iotaHom_iotaHom (P X.switchAll)).symm.trans
    (congrArg iotaHom (congrFun (coefficient_transport
      (fun D : Diagram => iotaHom (P D.switchAll)) P ueq_iota_switchAll_rcompetitor
      P_rcompetitor) X))

/-! ### 8.5 Unit U-ROT: "Rotate coordinates so that u is the downward vertical" (sm-3:4428-4429),
applied to the SMOOTH curve only — legitimate because the record (`RecordCarried`, and the
`HeightMarking` the lift produces) is record-level (FR-FL-C6). -/

/-- the rotation of the plane by the angle `φ` -/
def rotPlane (φ : ℝ) (p : Plane) : Plane :=
  (Real.cos φ * p.1 - Real.sin φ * p.2, Real.sin φ * p.1 + Real.cos φ * p.2)

/-- the downward vertical direction of the `xz` page -/
def downDir : Plane := ((0 : ℝ), (-1 : ℝ))

/-! ### U-ROT helpers -/

/-- (U-ROT helper) `rotPlane φ` is homogeneous -/
theorem urot_rotPlane_smul (φ r : ℝ) (p : Plane) : rotPlane φ (r • p) = r • rotPlane φ p := by
  simp only [rotPlane, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ext <;> dsimp <;> ring

/-- (U-ROT helper) `rotPlane φ` is additive -/
theorem urot_rotPlane_add (φ : ℝ) (p q : Plane) :
    rotPlane φ (p + q) = rotPlane φ p + rotPlane φ q := by
  simp only [rotPlane, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  ext <;> dsimp <;> ring

/-- (U-ROT helper) the rotation by `−φ` undoes the rotation by `φ` -/
theorem urot_rotPlane_neg_rotPlane (φ : ℝ) (p : Plane) : rotPlane (-φ) (rotPlane φ p) = p := by
  have h := Real.cos_sq_add_sin_sq φ
  simp only [rotPlane, Real.cos_neg, Real.sin_neg]
  ext
  · dsimp; linear_combination p.1 * h
  · dsimp; linear_combination p.2 * h

/-- (U-ROT helper) `rotPlane φ` is injective -/
theorem urot_rotPlane_injective (φ : ℝ) : Function.Injective (rotPlane φ) := by
  intro p q hpq
  rw [← urot_rotPlane_neg_rotPlane φ p, ← urot_rotPlane_neg_rotPlane φ q, hpq]

/-- (U-ROT helper) `det` is rotation-invariant -/
theorem urot_det_rotPlane (φ : ℝ) (a b : Plane) : det (rotPlane φ a) (rotPlane φ b) = det a b := by
  have h := Real.cos_sq_add_sin_sq φ
  simp only [det, rotPlane]
  linear_combination (a.1 * b.2 - a.2 * b.1) * h

/-- (U-ROT helper) the Euclidean length is rotation-invariant -/
theorem urot_euclideanLength_rotPlane (φ : ℝ) (p : Plane) :
    euclideanLength (rotPlane φ p) = euclideanLength p := by
  have h := Real.cos_sq_add_sin_sq φ
  rw [euclideanLength_formula, euclideanLength_formula]
  congr 1
  simp only [rotPlane]
  linear_combination (p.1 * p.1 + p.2 * p.2) * h

/-- (U-ROT helper) normalisation commutes with the rotation -/
theorem urot_normalize_rotPlane (φ : ℝ) (p : Plane) :
    SM.normalize (rotPlane φ p) = rotPlane φ (SM.normalize p) := by
  simp only [SM.normalize, urot_euclideanLength_rotPlane, urot_rotPlane_smul]

/-- (U-ROT helper) the rotation carries the unit vector of angle `α` to that of angle `α + φ` -/
theorem urot_rotPlane_cos_sin (φ α : ℝ) :
    rotPlane φ (Real.cos α, Real.sin α) = (Real.cos (α + φ), Real.sin (α + φ)) := by
  simp only [rotPlane, Real.cos_add, Real.sin_add]
  ext <;> dsimp <;> ring

/-- (U-ROT helper) a unit vector is `(cos α, sin α)` for its argument `α` -/
theorem urot_unit_eq_cos_sin (u : Plane) (hu : euclideanLength u = 1) :
    u = (Real.cos (Complex.arg (planeComplex u)), Real.sin (Complex.arg (planeComplex u))) := by
  have h := CornerRounding.G1_smul_dirOf_arg u
  rw [hu, one_smul] at h
  exact h.symm

/-- (U-ROT helper) the angle `φ_u := −π/2 − arg u` rotates the unit vector `u` to the downward vertical -/
theorem urot_rotPlane_unit_eq_downDir (u : Plane) (hu : euclideanLength u = 1) :
    rotPlane (-(Real.pi / 2) - Complex.arg (planeComplex u)) u = downDir := by
  have h := urot_unit_eq_cos_sin u hu
  generalize Complex.arg (planeComplex u) = α at h ⊢
  rw [h, urot_rotPlane_cos_sin]
  have hα : α + (-(Real.pi / 2) - α) = -(Real.pi / 2) := by ring
  rw [hα, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  rfl

/-- (U-ROT helper) `rotPlane φ` as a linear map -/
def urot_rotLin (φ : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun := rotPlane φ
  map_add' := urot_rotPlane_add φ
  map_smul' r p := urot_rotPlane_smul φ r p

/-- (U-ROT helper) `rotPlane φ` as a continuous linear map (finite-dimensional domain) -/
def urot_rotCLM (φ : ℝ) : Plane →L[ℝ] Plane := LinearMap.toContinuousLinearMap (urot_rotLin φ)

theorem urot_rotCLM_apply (φ : ℝ) (p : Plane) : urot_rotCLM φ p = rotPlane φ p := rfl

theorem urot_rotCLM_coe (φ : ℝ) : ⇑(urot_rotCLM φ) = rotPlane φ := rfl

/-- (U-ROT helper) the rotated curve is `C^∞` -/
theorem urot_smooth (φ : ℝ) (F : SmoothLoop) : ContDiff ℝ ∞ (rotPlane φ ∘ F.γ) := by
  rw [← urot_rotCLM_coe]
  exact (urot_rotCLM φ).contDiff.comp F.smooth

/-- (U-ROT helper) the rotated curve is 1-periodic -/
theorem urot_periodic (φ : ℝ) (F : SmoothLoop) : Function.Periodic (rotPlane φ ∘ F.γ) 1 :=
  F.periodic.comp (rotPlane φ)

/-- (U-ROT helper) the velocity of the rotated curve is the rotated velocity -/
theorem urot_hasDerivAt (φ : ℝ) (F : SmoothLoop) (t : ℝ) :
    HasDerivAt (rotPlane φ ∘ F.γ) (rotPlane φ (deriv F.γ t)) t := by
  have h := (urot_rotCLM φ).hasFDerivAt.comp_hasDerivAt t (F.hasDerivAt t)
  rw [urot_rotCLM_coe] at h
  exact h

theorem urot_deriv (φ : ℝ) (F : SmoothLoop) (t : ℝ) :
    deriv (rotPlane φ ∘ F.γ) t = rotPlane φ (deriv F.γ t) :=
  (urot_hasDerivAt φ F t).deriv

/-- (U-ROT helper) the rotated regular loop -/
def urot_loop (φ : ℝ) (F : SmoothRegularLoop) : SmoothRegularLoop where
  γ := rotPlane φ ∘ F.γ
  smooth := urot_smooth φ F.toSmoothLoop
  periodic := urot_periodic φ F.toSmoothLoop
  regular := fun t => by
    rw [urot_deriv]
    intro h
    apply F.regular t
    have h0 : rotPlane φ (0 : Plane) = 0 := by
      simp only [rotPlane]; ext <;> dsimp <;> ring
    exact urot_rotPlane_injective φ (h.trans h0.symm)

theorem urot_loop_γ (φ : ℝ) (F : SmoothRegularLoop) : (urot_loop φ F).γ = rotPlane φ ∘ F.γ := rfl

theorem urot_loop_deriv (φ : ℝ) (F : SmoothRegularLoop) (t : ℝ) :
    deriv (urot_loop φ F).γ t = rotPlane φ (deriv F.γ t) :=
  urot_deriv φ F.toSmoothLoop t

/-- (U-ROT helper) the polygonal record is carried by the rotated loop with the same parameters -/
def urot_recordCarried (φ : ℝ) {F : SmoothRegularLoop} {X : Diagram} (c : RecordCarried F X) :
    RecordCarried (urot_loop φ F) X where
  one := c.one
  τ := c.τ
  τ_mem := c.τ_mem
  τ_inj := c.τ_inj
  twin_eval := fun v => by
    show rotPlane φ (F.γ (c.τ v)) = rotPlane φ (F.γ (c.τ (X.twin v)))
    rw [c.twin_eval v]
  doubles := fun s t hs ht hst hγ => by
    apply c.doubles s t hs ht hst
    exact urot_rotPlane_injective φ hγ
  transverse := fun v => by
    rw [urot_loop_deriv, urot_loop_deriv, urot_det_rotPlane]
    exact c.transverse v
  order := c.order
  sign_eq := fun x => by
    rw [urot_loop_deriv, urot_loop_deriv, urot_det_rotPlane]
    exact c.sign_eq x

/-- (U-ROT) a record-carrying regular loop may be rotated so that a given unit direction becomes the
downward vertical; the polygonal record is untouched (`det` is rotation-invariant), every unit
tangent is rotated -/
theorem urot_exists_rotated (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X) (u : Plane)
    (hu : euclideanLength u = 1) :
    ∃ (φ : ℝ) (G : SmoothRegularLoop), G.γ = rotPlane φ ∘ F.γ ∧ Nonempty (RecordCarried G X) ∧
      ∀ t, SM.normalize (deriv G.γ t) = downDir ↔ SM.normalize (deriv F.γ t) = u := by
  set φ : ℝ := -(Real.pi / 2) - Complex.arg (planeComplex u) with hφ
  refine ⟨φ, urot_loop φ F, rfl, ⟨urot_recordCarried φ c⟩, fun t => ?_⟩
  rw [urot_loop_deriv, urot_normalize_rotPlane, ← urot_rotPlane_unit_eq_downDir u hu]
  exact (urot_rotPlane_injective φ).eq_iff


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

/-! #### Unit U-LIFT-1 (`ul1_`): the analytic helpers L1-L4 of PLAN_FINAL.md §3 (C) step 6, exported for
U-LIFT-2 (L5-L8) and U-LIFT-3 (L9-L10).  L1 `v + z′ > 0` (`ul1_length_add_snd_pos`, `ul1_denom_pos`);
L2 `liftY0` `C^∞` and 1-periodic (`ul1_liftY0_contDiff`, `ul1_liftY0_periodic`, loop forms); L3 display (*)
`z′ − y₀ x′ = v` (`ul1_liftY0_identity`, `ul1_liftY0_admissible`); L4 `circBump` `C^∞`, 1-periodic, `= 1` at the
centre and its integer translates, `= 0` at circle distance `≥ δ`, values in `[0, 1]` (`ul1_circBump_*`,
`0 < δ < 1/2`).  Smoothness of the speed `|γ′|` goes through `√g = exp (log g / 2)` because Mathlib's
`ContDiff.sqrt` / `ContDiff.norm` / `Real.contDiffAt_log` are not in this file's import closure. -/

/-- `|u|² = u.1² + u.2²` (local form of the accepted `euclideanLength_mul_self`, whose module is
not in this file's import closure) -/
theorem ul1_length_mul_self (u : Plane) :
    euclideanLength u * euclideanLength u = u.1 * u.1 + u.2 * u.2 := by
  rw [euclideanLength_formula]
  exact Real.mul_self_sqrt (by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2])

/-- `|u.2| ≤ |u|` -/
theorem ul1_abs_snd_le_length (u : Plane) : |u.2| ≤ euclideanLength u := by
  rw [euclideanLength_formula, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [mul_self_nonneg u.1]

/-- `|u.1| ≤ |u|` -/
theorem ul1_abs_fst_le_length (u : Plane) : |u.1| ≤ euclideanLength u := by
  rw [euclideanLength_formula, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [mul_self_nonneg u.2]

/-- a downward vertical vector normalises to `downDir` -/
theorem ul1_normalize_vertical_neg {z : ℝ} (hz : z < 0) :
    SM.normalize ((0 : ℝ), z) = downDir := by
  have hlen : euclideanLength ((0 : ℝ), z) = -z := by
    rw [euclideanLength_formula]
    simp only [mul_zero, zero_add]
    rw [Real.sqrt_mul_self_eq_abs, abs_of_neg hz]
  unfold normalize downDir
  rw [hlen]
  ext
  · simp
  · simp only [Prod.smul_snd, smul_eq_mul]
    rw [inv_neg, neg_mul, inv_mul_cancel₀ hz.ne]

/-- L1: `v + z′ > 0` for a nonzero vector that is not the downward vertical -/
theorem ul1_length_add_snd_pos {u : Plane} (hu : u ≠ 0) (hd : SM.normalize u ≠ downDir) :
    0 < euclideanLength u + u.2 := by
  have h2 := ul1_abs_snd_le_length u
  have hL := euclideanLength_pos hu
  by_contra hle
  rw [not_lt] at hle
  have hneg : u.2 < 0 := by
    by_contra h
    rw [not_lt] at h
    linarith
  have heq : euclideanLength u = -u.2 := by
    have := neg_le_abs u.2
    linarith [abs_of_neg hneg]
  have hsq := ul1_length_mul_self u
  have h1 : u.1 = 0 := by
    rw [heq] at hsq
    have : u.1 * u.1 = 0 := by nlinarith
    exact mul_self_eq_zero.mp this
  apply hd
  have hu' : u = ((0 : ℝ), u.2) := Prod.ext h1 rfl
  rw [hu']
  exact ul1_normalize_vertical_neg hneg

/-- L1 on a curve: the denominator of `liftY0` is positive -/
theorem ul1_denom_pos (γ : ℝ → Plane) (s : ℝ) (hreg : deriv γ s ≠ 0)
    (hd : SM.normalize (deriv γ s) ≠ downDir) :
    0 < euclideanLength (deriv γ s) + (deriv γ s).2 :=
  ul1_length_add_snd_pos hreg hd

/-- L3, display (*): `z′ − y₀ x′ = v` -/
theorem ul1_liftY0_identity (γ : ℝ → Plane) (s : ℝ)
    (hpos : 0 < euclideanLength (deriv γ s) + (deriv γ s).2) :
    (deriv γ s).2 - liftY0 γ s * (deriv γ s).1 = euclideanLength (deriv γ s) := by
  have hsq := ul1_length_mul_self (deriv γ s)
  have hne := hpos.ne'
  unfold liftY0
  field_simp
  linear_combination (-1 : ℝ) * hsq

/-- L3 corollary: `y₀` itself is an admissible constant -/
theorem ul1_liftY0_admissible (γ : ℝ → Plane) (s : ℝ) (hreg : deriv γ s ≠ 0)
    (hd : SM.normalize (deriv γ s) ≠ downDir) : LiftAdmissible γ s (liftY0 γ s) := by
  unfold LiftAdmissible
  rw [ul1_liftY0_identity γ s (ul1_denom_pos γ s hreg hd)]
  exact euclideanLength_pos hreg

/-- `log` has derivative `x⁻¹` at `x > 0`, derived from `exp` by the local-inverse rule (the
Mathlib module `Log.Deriv` is not in this file's import closure) -/
theorem ul1_hasDerivAt_log {x : ℝ} (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by
  have h := HasStrictDerivAt.of_local_left_inverse (f := Real.exp) (g := Real.log)
    (Real.continuousAt_log hx.ne') (Real.hasStrictDerivAt_exp (Real.log x)) (Real.exp_pos _).ne' ?_
  · rw [Real.exp_log hx] at h
    exact h.hasDerivAt
  · filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.exp_log hy

/-- `log ∘ g` is `C^∞` for a positive `C^∞` function `g`: its derivative `g′/g` is `C^∞`
(`contDiff_infty_iff_deriv`, not circular) -/
theorem ul1_contDiff_log_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ s, 0 < g s) :
    ContDiff ℝ ∞ (fun s => Real.log (g s)) := by
  have hdiff : ∀ s, HasDerivAt (fun s => Real.log (g s)) (deriv g s / g s) s := by
    intro s
    have hgs : HasDerivAt g (deriv g s) s := (hg.differentiable (by decide) s).hasDerivAt
    have h := (ul1_hasDerivAt_log (hpos s)).comp s hgs
    rw [div_eq_inv_mul]
    exact h
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun s => (hdiff s).differentiableAt, ?_⟩
  have hderiv : deriv (fun s => Real.log (g s)) = fun s => deriv g s / g s := by
    funext s; exact (hdiff s).deriv
  rw [hderiv]
  exact ((contDiff_infty_iff_deriv.mp hg).2).div hg (fun s => (hpos s).ne')

/-- `√g` is `C^∞` for a positive `C^∞` function `g` (as `exp (log g / 2)`; Mathlib's
`ContDiff.sqrt` is not in this file's import closure) -/
theorem ul1_contDiff_sqrt_comp {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ s, 0 < g s) :
    ContDiff ℝ ∞ (fun s => Real.sqrt (g s)) := by
  have hfun : (fun s => Real.sqrt (g s)) = fun s => Real.exp (Real.log (g s) * (1 / 2)) := by
    funext s
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hpos s)]
  rw [hfun]
  exact Real.contDiff_exp.comp ((ul1_contDiff_log_comp hg hpos).mul contDiff_const)

/-- the speed `s ↦ |γ′(s)|` of a `C^∞` regular curve is `C^∞` -/
theorem ul1_length_deriv_contDiff (γ : ℝ → Plane) (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ s, deriv γ s ≠ 0) : ContDiff ℝ ∞ (fun s => euclideanLength (deriv γ s)) := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  have hfun : (fun s => euclideanLength (deriv γ s)) =
      fun s => Real.sqrt ((deriv γ s).1 * (deriv γ s).1 + (deriv γ s).2 * (deriv γ s).2) := by
    funext s; exact euclideanLength_formula _
  rw [hfun]
  apply ul1_contDiff_sqrt_comp
  · exact (hd.fst.mul hd.fst).add (hd.snd.mul hd.snd)
  · intro s
    exact planeDot_self_pos (hreg s)

/-- L2: `y₀` is `C^∞` on a `C^∞` regular curve without downward vertical tangency -/
theorem ul1_liftY0_contDiff (γ : ℝ → Plane) (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ s, deriv γ s ≠ 0)
    (hdown : ∀ s, SM.normalize (deriv γ s) ≠ downDir) : ContDiff ℝ ∞ (liftY0 γ) := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  unfold liftY0
  apply ContDiff.div
  · exact hd.fst.neg
  · exact (ul1_length_deriv_contDiff γ hγ hreg).add hd.snd
  · intro s
    exact (ul1_denom_pos γ s (hreg s) (hdown s)).ne'

/-- L2: `y₀` is 1-periodic when the velocity is -/
theorem ul1_liftY0_periodic (γ : ℝ → Plane) (hper : Function.Periodic (deriv γ) 1) :
    Function.Periodic (liftY0 γ) 1 := by
  intro s
  simp only [liftY0, hper s]

theorem ul1_liftY0_add_one (γ : ℝ → Plane) (hper : Function.Periodic (deriv γ) 1) (s : ℝ) :
    liftY0 γ (s + 1) = liftY0 γ s :=
  ul1_liftY0_periodic γ hper s

/-- L2 on a regular loop -/
theorem ul1_liftY0_contDiff_loop (F : SmoothRegularLoop)
    (hdown : ∀ s, SM.normalize (deriv F.γ s) ≠ downDir) : ContDiff ℝ ∞ (liftY0 F.γ) :=
  ul1_liftY0_contDiff F.γ F.smooth F.regular hdown

theorem ul1_liftY0_periodic_loop (F : SmoothLoop) : Function.Periodic (liftY0 F.γ) 1 :=
  ul1_liftY0_periodic F.γ F.deriv_periodic

/-! L4: the circle bump -/

theorem ul1_circBump_contDiff (δ s₀ : ℝ) : ContDiff ℝ ∞ (circBump δ s₀) := by
  unfold circBump
  fun_prop

theorem ul1_circBump_add_one (δ s₀ s : ℝ) : circBump δ s₀ (s + 1) = circBump δ s₀ s := by
  have h : 2 * Real.pi * (s + 1 - s₀) = 2 * Real.pi * (s - s₀) + 2 * Real.pi := by ring
  simp only [circBump, h, Real.cos_add_two_pi]

theorem ul1_circBump_periodic (δ s₀ : ℝ) : Function.Periodic (circBump δ s₀) 1 :=
  fun s => ul1_circBump_add_one δ s₀ s

theorem ul1_circBump_add_int (δ s₀ s : ℝ) (n : ℤ) : circBump δ s₀ (s + n) = circBump δ s₀ s := by
  have h := (ul1_circBump_periodic δ s₀).int_mul n s
  simpa using h

theorem ul1_circBump_nonneg (δ s₀ s : ℝ) : 0 ≤ circBump δ s₀ s :=
  Real.smoothTransition.nonneg _

theorem ul1_circBump_le_one (δ s₀ s : ℝ) : circBump δ s₀ s ≤ 1 :=
  Real.smoothTransition.le_one _

theorem ul1_circBump_mem_Icc (δ s₀ s : ℝ) : circBump δ s₀ s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ul1_circBump_nonneg δ s₀ s, ul1_circBump_le_one δ s₀ s⟩

theorem ul1_cos_two_pi_mul_lt_one {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Real.cos (2 * Real.pi * δ) < 1 := by
  have hpi := Real.pi_pos
  have h0 : 0 < 2 * Real.pi * δ := by positivity
  have h1 : 2 * Real.pi * δ ≤ Real.pi := by nlinarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) h1 h0
  rwa [Real.cos_zero] at this

/-- L4: the bump is `1` at its centre -/
theorem ul1_circBump_self (δ s₀ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) : circBump δ s₀ s₀ = 1 := by
  unfold circBump
  have hne : 1 - Real.cos (2 * Real.pi * δ) ≠ 0 :=
    (sub_pos.mpr (ul1_cos_two_pi_mul_lt_one hδ hδ')).ne'
  rw [sub_self, mul_zero, Real.cos_zero, div_self hne]
  exact Real.smoothTransition.one

/-- L4: the bump is `1` at every integer translate of its centre -/
theorem ul1_circBump_eq_one (δ s₀ s : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (n : ℤ)
    (hs : s = s₀ + n) : circBump δ s₀ s = 1 := by
  rw [hs, ul1_circBump_add_int, ul1_circBump_self δ s₀ hδ hδ']

/-- L4: the bump vanishes at circle distance `≥ δ` from its centre -/
theorem ul1_circBump_eq_zero (δ s₀ s : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : ∀ n : ℤ, δ ≤ |s - s₀ - n|) : circBump δ s₀ s = 0 := by
  unfold circBump
  apply Real.smoothTransition.zero_of_nonpos
  have hden : 0 < 1 - Real.cos (2 * Real.pi * δ) :=
    sub_pos.mpr (ul1_cos_two_pi_mul_lt_one hδ hδ')
  apply div_nonpos_of_nonpos_of_nonneg _ hden.le
  rw [sub_nonpos]
  have hpi := Real.pi_pos
  set n : ℤ := round (s - s₀) with hn
  set d : ℝ := s - s₀ - n with hd
  have hd1 : |d| ≤ 1 / 2 := abs_sub_round (s - s₀)
  have hd2 : δ ≤ |d| := h n
  have hcos : Real.cos (2 * Real.pi * (s - s₀)) = Real.cos (2 * Real.pi * |d|) := by
    have : 2 * Real.pi * (s - s₀) = 2 * Real.pi * d + n * (2 * Real.pi) := by
      rw [hd]; ring
    rw [this, Real.cos_add_int_mul_two_pi, ← Real.cos_abs (2 * Real.pi * d), abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hcos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · nlinarith
  · nlinarith

/-- L4 contrapositive: where the bump is nonzero, the parameter is within circle distance `< δ` -/
theorem ul1_exists_int_of_circBump_ne_zero (δ s₀ s : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (h : circBump δ s₀ s ≠ 0) : ∃ n : ℤ, |s - s₀ - n| < δ := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact h (ul1_circBump_eq_zero δ s₀ s hδ hδ' hcon)

/-! Bonus for U-LIFT-2/3: `liftY`, `liftT` smoothness/periodicity and the coordinate identities -/

theorem ul1_liftY_contDiff (γ : ℝ → Plane) (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ s, deriv γ s ≠ 0)
    (hdown : ∀ s, SM.normalize (deriv γ s) ≠ downDir) {ι : Type} [Fintype ι] (τ c : ι → ℝ)
    (δ : ℝ) : ContDiff ℝ ∞ (liftY γ τ c δ) := by
  have h0 := ul1_liftY0_contDiff γ hγ hreg hdown
  unfold liftY
  apply h0.add
  apply ContDiff.sum
  intro v _
  exact (ul1_circBump_contDiff δ (τ v)).mul (contDiff_const.sub h0)

theorem ul1_liftY_add_one (γ : ℝ → Plane) (hper : Function.Periodic (deriv γ) 1)
    {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) :
    liftY γ τ c δ (s + 1) = liftY γ τ c δ s := by
  simp only [liftY, ul1_liftY0_add_one γ hper s, ul1_circBump_add_one]

theorem ul1_liftY_periodic (γ : ℝ → Plane) (hper : Function.Periodic (deriv γ) 1)
    {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) : Function.Periodic (liftY γ τ c δ) 1 :=
  fun s => ul1_liftY_add_one γ hper τ c δ s

theorem ul1_xOf_liftT (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) :
    xOf (liftT γ τ c δ) = fun s => (γ s).1 := rfl

theorem ul1_yOf_liftT (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) :
    yOf (liftT γ τ c δ) = liftY γ τ c δ := rfl

theorem ul1_zOf_liftT (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) :
    zOf (liftT γ τ c δ) = fun s => (γ s).2 := rfl

theorem ul1_xzOf_liftT (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) :
    xzOf (liftT γ τ c δ) = γ := by
  funext s; rfl

/-- the coordinates of a differentiable plane curve have the coordinates of its velocity as
derivatives -/
theorem ul1_hasDerivAt_fst (γ : ℝ → Plane) {s : ℝ} (h : HasDerivAt γ (deriv γ s) s) :
    HasDerivAt (fun t => (γ t).1) (deriv γ s).1 s :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s h

theorem ul1_hasDerivAt_snd (γ : ℝ → Plane) {s : ℝ} (h : HasDerivAt γ (deriv γ s) s) :
    HasDerivAt (fun t => (γ t).2) (deriv γ s).2 s :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt s h

theorem ul1_deriv_xOf_liftT (γ : ℝ → Plane) (hγ : Differentiable ℝ γ) {ι : Type} [Fintype ι]
    (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) : deriv (xOf (liftT γ τ c δ)) s = (deriv γ s).1 := by
  rw [ul1_xOf_liftT]
  exact (ul1_hasDerivAt_fst γ (hγ s).hasDerivAt).deriv

theorem ul1_deriv_zOf_liftT (γ : ℝ → Plane) (hγ : Differentiable ℝ γ) {ι : Type} [Fintype ι]
    (τ c : ι → ℝ) (δ : ℝ) (s : ℝ) : deriv (zOf (liftT γ τ c δ)) s = (deriv γ s).2 := by
  rw [ul1_zOf_liftT]
  exact (ul1_hasDerivAt_snd γ (hγ s).hasDerivAt).deriv

theorem ul1_liftT_contDiff (γ : ℝ → Plane) (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ s, deriv γ s ≠ 0)
    (hdown : ∀ s, SM.normalize (deriv γ s) ≠ downDir) {ι : Type} [Fintype ι] (τ c : ι → ℝ)
    (δ : ℝ) : ContDiff ℝ ∞ (liftT γ τ c δ) := by
  unfold liftT
  exact hγ.fst.prodMk ((ul1_liftY_contDiff γ hγ hreg hdown τ c δ).prodMk hγ.snd)

theorem ul1_liftT_periodic (γ : ℝ → Plane) (hγ : Function.Periodic γ 1)
    (hper : Function.Periodic (deriv γ) 1) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) :
    Function.Periodic (liftT γ τ c δ) 1 := by
  intro s
  simp only [liftT, hγ s, ul1_liftY_add_one γ hper τ c δ s]

/-- the loop forms -/
theorem ul1_liftT_contDiff_loop (F : SmoothRegularLoop)
    (hdown : ∀ s, SM.normalize (deriv F.γ s) ≠ downDir) {ι : Type} [Fintype ι] (τ c : ι → ℝ)
    (δ : ℝ) : ContDiff ℝ ∞ (liftT F.γ τ c δ) :=
  ul1_liftT_contDiff F.γ F.smooth F.regular hdown τ c δ

theorem ul1_liftT_periodic_loop (F : SmoothLoop) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ) :
    Function.Periodic (liftT F.γ τ c δ) 1 :=
  ul1_liftT_periodic F.γ F.periodic F.deriv_periodic τ c δ

/-- a nonzero vector that is not the downward vertical: if its first coordinate vanishes, its
second is positive -/
theorem ul2_snd_pos_of_fst_eq_zero (d : Plane) (hd : d ≠ 0) (hdown : SM.normalize d ≠ downDir)
    (h1 : d.1 = 0) : 0 < d.2 := by
  by_contra hle
  have h2 : d.2 < 0 := lt_of_le_of_ne (not_lt.mp hle) (fun h => hd (Prod.ext h1 h))
  apply hdown
  have hlen : euclideanLength d = -d.2 := by
    rw [euclideanLength_formula, h1, zero_mul, zero_add, Real.sqrt_mul_self_eq_abs, abs_of_neg h2]
  unfold SM.normalize downDir
  rw [hlen]
  refine Prod.ext ?_ ?_
  · show (-d.2)⁻¹ * d.1 = 0
    rw [h1, mul_zero]
  · show (-d.2)⁻¹ * d.2 = -1
    rw [inv_mul_eq_div, div_eq_iff (neg_ne_zero.mpr h2.ne)]
    ring

/-- an admissible constant exists at every velocity that is not the downward vertical -/
theorem ul2_exists_admissible_vec (d : Plane) (hd : d ≠ 0) (hdown : SM.normalize d ≠ downDir) :
    ∃ c : ℝ, 0 < d.2 - c * d.1 := by
  rcases lt_trichotomy d.1 0 with hx | hx | hx
  · refine ⟨d.2 / d.1 + 1, ?_⟩
    have hmd : d.2 / d.1 * d.1 = d.2 := div_mul_cancel₀ d.2 hx.ne
    have : d.2 - (d.2 / d.1 + 1) * d.1 = -d.1 := by linear_combination (-1 : ℝ) * hmd
    rw [this]; linarith
  · refine ⟨0, ?_⟩
    rw [zero_mul, sub_zero]
    exact ul2_snd_pos_of_fst_eq_zero d hd hdown hx
  · refine ⟨d.2 / d.1 - 1, ?_⟩
    have hmd : d.2 / d.1 * d.1 = d.2 := div_mul_cancel₀ d.2 hx.ne'
    have : d.2 - (d.2 / d.1 - 1) * d.1 = d.1 := by linear_combination (-1 : ℝ) * hmd
    rw [this]; exact hx

/-- the five-case choice of `c_O < c_U` on two velocities (vector form of `ul_exists_constants`):
the determinant is used only when `x′_O < 0 < x′_U` -/
theorem ul2_exists_constants_vec (dO dU : Plane) (hO : dO ≠ 0) (hU : dU ≠ 0)
    (hdO : SM.normalize dO ≠ downDir) (hdU : SM.normalize dU ≠ downDir)
    (hdet : det dO dU < 0) :
    ∃ cO cU : ℝ, cO < cU ∧ 0 < dO.2 - cO * dO.1 ∧ 0 < dU.2 - cU * dU.1 := by
  by_cases hcase : dO.1 < 0 ∧ 0 < dU.1
  · obtain ⟨hxO, hxU⟩ := hcase
    have hmdO : dO.2 / dO.1 * dO.1 = dO.2 := div_mul_cancel₀ dO.2 hxO.ne
    have hmdU : dU.2 / dU.1 * dU.1 = dU.2 := div_mul_cancel₀ dU.2 hxU.ne'
    have hm : dO.2 / dO.1 < dU.2 / dU.1 := by
      have key : 0 < dU.2 / dU.1 - dO.2 / dO.1 := by
        rw [div_sub_div _ _ hxU.ne' hxO.ne]
        apply div_pos_of_neg_of_neg
        · unfold det at hdet; linarith
        · nlinarith
      linarith
    refine ⟨(2 * (dO.2 / dO.1) + dU.2 / dU.1) / 3, (dO.2 / dO.1 + 2 * (dU.2 / dU.1)) / 3,
      by linarith, ?_, ?_⟩
    · have : dO.2 - (2 * (dO.2 / dO.1) + dU.2 / dU.1) / 3 * dO.1
          = dO.1 * (dO.2 / dO.1 - (2 * (dO.2 / dO.1) + dU.2 / dU.1) / 3) := by
        linear_combination (-1 : ℝ) * hmdO
      rw [this]
      exact mul_pos_of_neg_of_neg hxO (by linarith)
    · have : dU.2 - (dO.2 / dO.1 + 2 * (dU.2 / dU.1)) / 3 * dU.1
          = dU.1 * (dU.2 / dU.1 - (dO.2 / dO.1 + 2 * (dU.2 / dU.1)) / 3) := by
        linear_combination (-1 : ℝ) * hmdU
      rw [this]
      exact mul_pos hxU (by linarith)
  · rcases not_and_or.mp hcase with hO' | hU'
    · have hO'' : 0 ≤ dO.1 := not_lt.mp hO'
      obtain ⟨cU, hcU⟩ := ul2_exists_admissible_vec dU hU hdU
      refine ⟨min (cU - 1) (dO.2 / dO.1 - 1), cU, lt_of_le_of_lt (min_le_left _ _) (by linarith),
        ?_, hcU⟩
      rcases hO''.lt_or_eq with hpos | hzero
      · have hle : min (cU - 1) (dO.2 / dO.1 - 1) ≤ dO.2 / dO.1 - 1 := min_le_right _ _
        have hmd : dO.2 / dO.1 * dO.1 = dO.2 := div_mul_cancel₀ dO.2 hpos.ne'
        have h1 : (dO.2 / dO.1 - 1) * dO.1 = dO.2 - dO.1 := by linear_combination hmd
        have h2 := mul_le_mul_of_nonneg_right hle hpos.le
        linarith
      · rw [← hzero, mul_zero, sub_zero]
        exact ul2_snd_pos_of_fst_eq_zero dO hO hdO hzero.symm
    · have hU'' : dU.1 ≤ 0 := not_lt.mp hU'
      obtain ⟨cO, hcO⟩ := ul2_exists_admissible_vec dO hO hdO
      refine ⟨cO, max (cO + 1) (dU.2 / dU.1 + 1), lt_of_lt_of_le (by linarith) (le_max_left _ _),
        hcO, ?_⟩
      rcases hU''.lt_or_eq with hneg | hzero
      · have hle : dU.2 / dU.1 + 1 ≤ max (cO + 1) (dU.2 / dU.1 + 1) := le_max_right _ _
        have hmd : dU.2 / dU.1 * dU.1 = dU.2 := div_mul_cancel₀ dU.2 hneg.ne
        have h1 : (dU.2 / dU.1 + 1) * dU.1 = dU.2 + dU.1 := by linear_combination hmd
        have h2 := mul_le_mul_of_nonpos_right hle hneg.le
        linarith
      · rw [hzero, mul_zero, sub_zero]
        exact ul2_snd_pos_of_fst_eq_zero dU hU hdU hzero

/-- (U-LIFT-2) sm-3:4477-4494: at a negative double point (`det(t_O, t_U) < 0`) of a curve without
downward vertical tangency there are admissible constants `c_O < c_U` — five cases on the signs of
`x′_O, x′_U`, the determinant used only when `x′_O < 0 < x′_U`; vertical branches (`x′ = 0`, hence
`z′ > 0`) impose no constraint (FR-FL-C7) -/
theorem ul_exists_constants (γ : ℝ → Plane) (sO sU : ℝ) (hO : deriv γ sO ≠ 0) (hU : deriv γ sU ≠ 0)
    (hdO : SM.normalize (deriv γ sO) ≠ downDir) (hdU : SM.normalize (deriv γ sU) ≠ downDir)
    (hdet : det (deriv γ sO) (deriv γ sU) < 0) :
    ∃ cO cU : ℝ, cO < cU ∧ LiftAdmissible γ sO cO ∧ LiftAdmissible γ sU cU := by
  exact ul2_exists_constants_vec _ _ hO hU hdO hdU hdet

/-! Helpers of U-LIFT-2 (L6-L8) for the transverse lift, consumed by `ulift_exists_transverse_lift`:
the bump facts needed for the disjoint supports, the choice of `δ` (below `1/4`, below half the minimal
circle gap of the `τ v`, below every admissibility radius), the single-bump reduction of `liftY`
(`Finset.sum_eq_single`), `y (τ v) = c v` (L8) and the positivity `z′ − y x′ > 0` (L7). -/

theorem ul2_circBump_nonneg (δ s₀ s : ℝ) : 0 ≤ circBump δ s₀ s :=
  Real.smoothTransition.nonneg _

theorem ul2_circBump_le_one (δ s₀ s : ℝ) : circBump δ s₀ s ≤ 1 :=
  Real.smoothTransition.le_one _

/-- `cos (2πδ) < 1` for `0 < δ < 1` -/
theorem ul2_cos_two_pi_mul_lt_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    Real.cos (2 * Real.pi * δ) < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one _) fun h => ?_
  have hpi := Real.pi_pos
  rw [Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith) (by nlinarith)] at h
  nlinarith

/-- the bump equals `1` at its centre (`0 < δ < 1`) -/
theorem ul2_circBump_self {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) (s₀ : ℝ) : circBump δ s₀ s₀ = 1 := by
  unfold circBump
  rw [sub_self, mul_zero, Real.cos_zero, div_self (by linarith [ul2_cos_two_pi_mul_lt_one h0 h1])]
  exact Real.smoothTransition.one

/-- the bump vanishes at circle distance `≥ δ` from its centre (`δ ≤ 1/2`) -/
theorem ul2_circBump_eq_zero {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) (s₀ s : ℝ)
    (hfar : ∀ n : ℤ, δ ≤ |s - s₀ - n|) : circBump δ s₀ s = 0 := by
  unfold circBump
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · have hpi := Real.pi_pos
    set n : ℤ := round (s - s₀) with hn
    have hr : |s - s₀ - n| ≤ 1 / 2 := abs_sub_round (s - s₀)
    have hδr := hfar n
    have hcos : Real.cos (2 * Real.pi * (s - s₀)) = Real.cos (2 * Real.pi * |s - s₀ - n|) := by
      have e1 : 2 * Real.pi * |s - s₀ - n| = |2 * Real.pi * (s - s₀ - n)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have e2 : 2 * Real.pi * (s - s₀) = 2 * Real.pi * (s - s₀ - n) + n * (2 * Real.pi) := by ring
      rw [e1, Real.cos_abs, e2, Real.cos_add_int_mul_two_pi]
    rw [hcos]
    have : Real.cos (2 * Real.pi * |s - s₀ - n|) ≤ Real.cos (2 * Real.pi * δ) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith)
    linarith
  · linarith [Real.cos_le_one (2 * Real.pi * δ)]

/-- a nonvanishing bump value puts the parameter within circle distance `< δ` of the centre -/
theorem ul2_exists_int_of_circBump_ne_zero {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) {s₀ s : ℝ}
    (hne : circBump δ s₀ s ≠ 0) : ∃ n : ℤ, |s - s₀ - n| < δ := by
  by_contra hcon
  refine hne (ul2_circBump_eq_zero h0 h1 s₀ s fun n => ?_)
  exact not_lt.mp fun h => hcon ⟨n, h⟩

/-- the circle gap of two distinct points of `[0, 1)` -/
theorem ul2_gap_of_mem_Ico {a b : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) (hb : b ∈ Set.Ico (0 : ℝ) 1)
    (n : ℤ) : min |a - b| (1 - |a - b|) ≤ |a - b - n| := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hd1 : |a - b| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hle := le_abs_self (a - b)
  have hnle := neg_abs_le (a - b)
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn1 : n ≤ -1 := by omega
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
    have : 1 - |a - b| ≤ |a - b - n| := by
      rw [abs_of_pos (show (0 : ℝ) < a - b - n by linarith)]; linarith
    exact le_trans (min_le_right _ _) this
  · subst hn; simp
  · have hn1 : 1 ≤ n := by omega
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have : 1 - |a - b| ≤ |a - b - n| := by
      rw [abs_of_neg (show a - b - n < 0 by linarith)]; linarith
    exact le_trans (min_le_right _ _) this

theorem ul2_gap_pos {a b : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) (hb : b ∈ Set.Ico (0 : ℝ) 1)
    (hab : a ≠ b) : 0 < min |a - b| (1 - |a - b|) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hd1 : |a - b| < 1 := by rw [abs_lt]; constructor <;> linarith
  exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hab)) (by linarith)

/-- a finite family of positive reals has a positive lower bound -/
theorem ul2_exists_pos_le {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- admissibility is open: a radius around an admissible parameter -/
theorem ul2_exists_radius (γ : ℝ → Plane) (hcont : Continuous (deriv γ)) (s₀ c : ℝ)
    (h : LiftAdmissible γ s₀ c) : ∃ r : ℝ, 0 < r ∧ ∀ s, |s - s₀| < r → LiftAdmissible γ s c := by
  have hc : Continuous fun s => (deriv γ s).2 - c * (deriv γ s).1 :=
    hcont.snd.sub (continuous_const.mul hcont.fst)
  have hev : ∀ᶠ s in nhds s₀, (0 : ℝ) < (deriv γ s).2 - c * (deriv γ s).1 :=
    continuousAt_const.eventually_lt hc.continuousAt h
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hball⟩ := hev
  exact ⟨r, hr, fun s hs => hball (by rwa [Real.dist_eq])⟩

/-- (L6) the choice of `δ`: below `1/4`, below half the minimal circle gap of the (injective,
fundamental-period) parameters `τ v`, and below every admissibility radius -/
theorem ul2_exists_delta (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ)
    (hτ : ∀ v, τ v ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective τ)
    (hcont : Continuous (deriv γ)) (hper : Function.Periodic (deriv γ) 1)
    (hadm : ∀ v, LiftAdmissible γ (τ v) (c v)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
      (∀ v w, v ≠ w → ∀ n : ℤ, 2 * δ ≤ |τ v - τ w - n|) ∧
      (∀ v s, (∃ n : ℤ, |s - τ v - n| < δ) → LiftAdmissible γ s (c v)) := by
  -- the circle gaps
  let g : ι × ι → ℝ := fun p =>
    if p.1 = p.2 then 1 else min |τ p.1 - τ p.2| (1 - |τ p.1 - τ p.2|)
  have hg : ∀ p, 0 < g p := by
    intro p
    simp only [g]
    split_ifs with h
    · exact one_pos
    · exact ul2_gap_pos (hτ _) (hτ _) (fun e => h (hinj e))
  obtain ⟨ε₁, hε₁, hε₁le⟩ := ul2_exists_pos_le g hg
  -- the admissibility radii
  choose r hr using fun v => ul2_exists_radius γ hcont (τ v) (c v) (hadm v)
  obtain ⟨ε₂, hε₂, hε₂le⟩ := ul2_exists_pos_le r fun v => (hr v).1
  refine ⟨min (min (ε₁ / 2) ε₂) (1 / 8), by positivity, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  · intro v w hvw n
    have h1 : min (min (ε₁ / 2) ε₂) (1 / 8) ≤ ε₁ / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 := hε₁le (v, w)
    have h3 : g (v, w) = min |τ v - τ w| (1 - |τ v - τ w|) := by
      simp [g, hvw]
    have h4 := ul2_gap_of_mem_Ico (hτ v) (hτ w) n
    linarith
  · rintro v s ⟨n, hn⟩
    have h1 : min (min (ε₁ / 2) ε₂) (1 / 8) ≤ ε₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 := (hr v).2 (s - n) (by
      have : s - n - τ v = s - τ v - n := by ring
      rw [this]; linarith [hε₂le v])
    have hp : deriv γ (s - n) = deriv γ s := by
      have := hper.sub_int_mul_eq (x := s) n
      simpa using this
    unfold LiftAdmissible at h2 ⊢
    rwa [hp] at h2

/-- (L6) at most one bump is nonzero at any parameter -/
theorem ul2_bump_unique {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) {ι : Type} (τ : ι → ℝ)
    (hgap : ∀ v w, v ≠ w → ∀ n : ℤ, 2 * δ ≤ |τ v - τ w - n|) {s : ℝ} {v w : ι}
    (hv : circBump δ (τ v) s ≠ 0) (hw : circBump δ (τ w) s ≠ 0) : v = w := by
  by_contra hne
  obtain ⟨n, hn⟩ := ul2_exists_int_of_circBump_ne_zero h0 h1 hv
  obtain ⟨m, hm⟩ := ul2_exists_int_of_circBump_ne_zero h0 h1 hw
  have hg := hgap v w hne (m - n)
  have heq : τ v - τ w - ((m - n : ℤ) : ℝ) = (s - τ w - m) - (s - τ v - n) := by
    push_cast; ring
  rw [heq] at hg
  rw [abs_lt] at hn hm
  rw [le_abs] at hg
  rcases hg with hg | hg <;> linarith

/-- (L6) the sum reduces to the single bump centred at `τ v` when the others vanish -/
theorem ul2_liftY_eq_single (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ s : ℝ)
    (v : ι) (hz : ∀ w, w ≠ v → circBump δ (τ w) s = 0) :
    liftY γ τ c δ s = liftY0 γ s + circBump δ (τ v) s * (c v - liftY0 γ s) := by
  unfold liftY
  rw [Finset.sum_eq_single v (fun w _ hw => by rw [hz w hw, zero_mul])
    (fun h => (h (Finset.mem_univ v)).elim)]

/-- (L6) the sum vanishes when every bump vanishes -/
theorem ul2_liftY_eq_liftY0 (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ s : ℝ)
    (hz : ∀ w, circBump δ (τ w) s = 0) : liftY γ τ c δ s = liftY0 γ s := by
  unfold liftY
  rw [Finset.sum_eq_zero (fun w _ => by rw [hz w, zero_mul]), add_zero]

/-- the bump is 1-periodic in the parameter -/
theorem ul2_circBump_periodic (δ s₀ : ℝ) : Function.Periodic (circBump δ s₀) 1 := by
  intro s
  unfold circBump
  have : 2 * Real.pi * (s + 1 - s₀) = 2 * Real.pi * (s - s₀) + 2 * Real.pi := by ring
  rw [this, Real.cos_add_two_pi]

/-- `y` is 1-periodic when `y₀` is -/
theorem ul2_liftY_periodic (γ : ℝ → Plane) {ι : Type} [Fintype ι] (τ c : ι → ℝ) (δ : ℝ)
    (h0 : Function.Periodic (liftY0 γ) 1) : Function.Periodic (liftY γ τ c δ) 1 := by
  intro s
  unfold liftY
  rw [h0 s]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ul2_circBump_periodic δ (τ v) s]

/-- (L8) `y (τ v) = c v` -/
theorem ul2_liftY_tau {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) (γ : ℝ → Plane) {ι : Type} [Fintype ι]
    (τ c : ι → ℝ) (hgap : ∀ v w, v ≠ w → ∀ n : ℤ, 2 * δ ≤ |τ v - τ w - n|) (v : ι) :
    liftY γ τ c δ (τ v) = c v := by
  have hz : ∀ w, w ≠ v → circBump δ (τ w) (τ v) = 0 := fun w hw =>
    ul2_circBump_eq_zero h0 h1 (τ w) (τ v) fun n => by linarith [hgap v w (Ne.symm hw) n]
  rw [ul2_liftY_eq_single γ τ c δ (τ v) v hz, ul2_circBump_self h0 (by linarith) (τ v)]
  ring

/-- (L7) `z′ − y x′ = (1 − b) (z′ − y₀ x′) + b (z′ − c_v x′) > 0` -/
theorem ul2_liftY_admissible {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) (γ : ℝ → Plane) {ι : Type}
    [Fintype ι] (τ c : ι → ℝ) (hgap : ∀ v w, v ≠ w → ∀ n : ℤ, 2 * δ ≤ |τ v - τ w - n|)
    (hadm : ∀ v s, (∃ n : ℤ, |s - τ v - n| < δ) → LiftAdmissible γ s (c v)) (s : ℝ)
    (hpos : 0 < (deriv γ s).2 - liftY0 γ s * (deriv γ s).1) :
    0 < (deriv γ s).2 - liftY γ τ c δ s * (deriv γ s).1 := by
  by_cases hex : ∃ v, circBump δ (τ v) s ≠ 0
  · obtain ⟨v, hv⟩ := hex
    have hz : ∀ w, w ≠ v → circBump δ (τ w) s = 0 := fun w hw => by
      by_contra hw'
      exact hw (ul2_bump_unique h0 h1 τ hgap hw' hv)
    rw [ul2_liftY_eq_single γ τ c δ s v hz]
    have hb0 : 0 ≤ circBump δ (τ v) s := ul2_circBump_nonneg _ _ _
    have hb1 : circBump δ (τ v) s ≤ 1 := ul2_circBump_le_one _ _ _
    have hadm' : 0 < (deriv γ s).2 - c v * (deriv γ s).1 :=
      hadm v s (ul2_exists_int_of_circBump_ne_zero h0 h1 hv)
    have hsplit : (deriv γ s).2 - (liftY0 γ s + circBump δ (τ v) s * (c v - liftY0 γ s)) * (deriv γ s).1
        = (1 - circBump δ (τ v) s) * ((deriv γ s).2 - liftY0 γ s * (deriv γ s).1)
          + circBump δ (τ v) s * ((deriv γ s).2 - c v * (deriv γ s).1) := by ring
    rw [hsplit]
    have hA := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - circBump δ (τ v) s) hpos.le
    have hB := mul_pos (lt_of_le_of_ne hb0 (Ne.symm hv)) hadm'
    linarith
  · have hz : ∀ w, circBump δ (τ w) s = 0 := fun w => by
      by_contra hw
      exact hex ⟨w, hw⟩
    rw [ul2_liftY_eq_liftY0 γ τ c δ s hz]
    exact hpos

/-! #### Unit U-LIFT-3 (`ul3_`): L9-L10 of PLAN_FINAL.md §3 (C) step 6 — the `TransverseKnot` built
from `liftT`, its `HeightMarking` reading of `X` (FR-FL-C8) and the front-writhe identity.  The data
of the lift (the constants `c_O < c_U` at every crossing and the bump radius `δ` with the L6
properties) is frozen as `ul3_LiftData`; the knot is `ul3_knot`, the reading `ul3_marking`. -/

/-! ##### The fundamental-period representative `Int.fract` -/

theorem ul3_fract_mem (s : ℝ) : Int.fract s ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩

theorem ul3_sameT_fract (s : ℝ) : SameT (Int.fract s) s :=
  ⟨⌊s⌋, (Int.fract_add_floor s).symm⟩

theorem ul3_fract_ne_of_not_sameT {s t : ℝ} (h : ¬ SameT s t) : Int.fract s ≠ Int.fract t := by
  intro heq
  apply h
  have h2 : SameT (Int.fract s) t := by rw [heq]; exact ul3_sameT_fract t
  exact (ul3_sameT_fract s).symm.trans h2

/-! ##### The constants on occurrences: `c_O` at the over occurrence, `c_U` at the under one -/

/-- the lift constant of an occurrence: `c_O` of its crossing at the over occurrence, `c_U` at the
under occurrence -/
def ul3_cst (X : Diagram) (cO cU : X.Γ.Crossing → ℝ) (v : X.Γ.Visit) : ℝ :=
  if X.isOver v then cO v.1 else cU v.1

theorem ul3_cst_overVisit (X : Diagram) (cO cU : X.Γ.Crossing → ℝ) (x : X.Γ.Crossing) :
    ul3_cst X cO cU (X.overVisit x) = cO x := by
  have h : X.isOver (X.overVisit x) := X.isOver_overVisit x
  simp [ul3_cst, h]

theorem ul3_cst_underVisit (X : Diagram) (cO cU : X.Γ.Crossing → ℝ) (x : X.Γ.Crossing) :
    ul3_cst X cO cU (X.underVisit x) = cU x := by
  have h : ¬ X.isOver (X.underVisit x) := X.not_isOver_underVisit x
  simp [ul3_cst, h]

/-- the smaller constant sits at the over occurrence -/
theorem ul3_cst_lt_twin_iff (X : Diagram) (cO cU : X.Γ.Crossing → ℝ) (hlt : ∀ x, cO x < cU x)
    (v : X.Γ.Visit) :
    ul3_cst X cO cU v < ul3_cst X cO cU (X.twin v) ↔ X.overBit v = true := by
  rcases X.visit_eq_over_or_under v with h | h
  · rw [h, Diagram.twin_overVisit, ul3_cst_overVisit, ul3_cst_underVisit, Diagram.overBit_overVisit]
    exact ⟨fun _ => rfl, fun _ => hlt v.1⟩
  · rw [h, Diagram.twin_underVisit, ul3_cst_overVisit, ul3_cst_underVisit,
      Diagram.overBit_underVisit]
    exact ⟨fun h' => absurd (lt_trans h' (hlt v.1)) (lt_irrefl _),
      fun h' => absurd h' Bool.false_ne_true⟩

/-- the two occurrences of a crossing carry distinct constants -/
theorem ul3_cst_ne_twin (X : Diagram) (cO cU : X.Γ.Crossing → ℝ) (hlt : ∀ x, cO x < cU x)
    (v : X.Γ.Visit) : ul3_cst X cO cU v ≠ ul3_cst X cO cU (X.twin v) := by
  rcases X.visit_eq_over_or_under v with h | h
  · rw [h, Diagram.twin_overVisit, ul3_cst_overVisit, ul3_cst_underVisit]
    exact (hlt v.1).ne
  · rw [h, Diagram.twin_underVisit, ul3_cst_overVisit, ul3_cst_underVisit]
    exact (hlt v.1).ne'

/-- at every (negative) crossing the over-first determinant of the carried loop is negative -/
theorem ul3_det_neg {F : SmoothRegularLoop} {X : Diagram} (c : RecordCarried F X)
    (hneg : ∀ x, X.sign x = -1) (x : X.Γ.Crossing) :
    det (deriv F.γ (c.τ (X.overVisit x))) (deriv F.γ (c.τ (X.underVisit x))) < 0 := by
  have h := c.sign_eq x
  rw [hneg x] at h
  exact _root_.sign_eq_neg_one_iff.mp h

/-- the integer value of a negative crossing sign -/
theorem ul3_sign_cast {X : Diagram} (hneg : ∀ x, X.sign x = -1) (x : X.Γ.Crossing) :
    ((X.sign x : SignType) : ℤ) = -1 := by
  rw [hneg x]
  rfl

/-- (L5 on the whole diagram) admissible constants `c_O < c_U` at every crossing, packaged on the
occurrences -/
theorem ul3_exists_cst (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X)
    (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (hneg : ∀ x, X.sign x = -1) :
    ∃ cO cU : X.Γ.Crossing → ℝ, (∀ x, cO x < cU x) ∧
      ∀ v, LiftAdmissible F.γ (c.τ v) (ul3_cst X cO cU v) := by
  have hx : ∀ x : X.Γ.Crossing, ∃ cO cU : ℝ, cO < cU ∧
      LiftAdmissible F.γ (c.τ (X.overVisit x)) cO ∧
      LiftAdmissible F.γ (c.τ (X.underVisit x)) cU := fun x =>
    ul_exists_constants F.γ _ _ (F.regular _) (F.regular _) (hdown _) (hdown _)
      (ul3_det_neg c hneg x)
  choose cO cU hlt hO hU using hx
  refine ⟨cO, cU, hlt, fun v => ?_⟩
  rcases X.visit_eq_over_or_under v with h | h
  · rw [h, ul3_cst_overVisit]; exact hO v.1
  · rw [h, ul3_cst_underVisit]; exact hU v.1

/-! ##### The data of the lift -/

/-- the data of the transverse lift of the carried loop `F`: the admissible constants `c_O < c_U`
at every crossing (L5) and the bump radius `δ` with the L6 properties (below `1/4`, bumps with
disjoint supports around the `τ v`, admissibility of `c_v` on the support of the bump at `τ v`) -/
structure ul3_LiftData (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X) where
  cO : X.Γ.Crossing → ℝ
  cU : X.Γ.Crossing → ℝ
  lt : ∀ x, cO x < cU x
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt : δ < 1 / 4
  gap : ∀ v w, v ≠ w → ∀ n : ℤ, 2 * δ ≤ |c.τ v - c.τ w - n|
  adm : ∀ v s, (∃ n : ℤ, |s - c.τ v - n| < δ) → LiftAdmissible F.γ s (ul3_cst X cO cU v)

/-- (L5 + L6) the data exists -/
theorem ul3_exists_liftData (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X)
    (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (hneg : ∀ x, X.sign x = -1) :
    Nonempty (ul3_LiftData F X c) := by
  obtain ⟨cO, cU, hlt, hadm⟩ := ul3_exists_cst F X c hdown hneg
  obtain ⟨δ, hδ0, hδ1, hgap, hadm'⟩ := ul2_exists_delta F.γ c.τ (ul3_cst X cO cU) c.τ_mem c.τ_inj
    F.toSmoothLoop.continuous_deriv F.toSmoothLoop.deriv_periodic hadm
  exact ⟨⟨cO, cU, hlt, δ, hδ0, hδ1, hgap, hadm'⟩⟩

/-- the constants as a function on occurrences -/
def ul3_cstOf {F : SmoothRegularLoop} {X : Diagram} {c : RecordCarried F X}
    (d : ul3_LiftData F X c) : X.Γ.Visit → ℝ :=
  ul3_cst X d.cO d.cU

/-- the lifted curve `s ↦ (x(s), y(s), z(s))` -/
def ul3_T {F : SmoothRegularLoop} {X : Diagram} {c : RecordCarried F X}
    (d : ul3_LiftData F X c) : ℝ → Space :=
  liftT F.γ c.τ (ul3_cstOf d) d.δ

section ul3_knot

variable {F : SmoothRegularLoop} {X : Diagram} {c : RecordCarried F X}

theorem ul3_xzOf_T (d : ul3_LiftData F X c) : xzOf (ul3_T d) = F.γ :=
  ul1_xzOf_liftT F.γ c.τ (ul3_cstOf d) d.δ

theorem ul3_yOf_T (d : ul3_LiftData F X c) : yOf (ul3_T d) = liftY F.γ c.τ (ul3_cstOf d) d.δ :=
  rfl

/-- (L8) the height at the occurrence `v` is its constant -/
theorem ul3_yOf_T_tau (d : ul3_LiftData F X c) (v : X.Γ.Visit) :
    yOf (ul3_T d) (c.τ v) = ul3_cstOf d v :=
  ul2_liftY_tau d.δ_pos (by linarith [d.δ_lt]) F.γ c.τ (ul3_cstOf d) d.gap v

theorem ul3_T_smooth (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) : ContDiff ℝ ∞ (ul3_T d) :=
  ul1_liftT_contDiff_loop F hdown c.τ (ul3_cstOf d) d.δ

theorem ul3_T_periodic (d : ul3_LiftData F X c) : Function.Periodic (ul3_T d) 1 :=
  ul1_liftT_periodic_loop F.toSmoothLoop c.τ (ul3_cstOf d) d.δ

theorem ul3_deriv_xOf_T (d : ul3_LiftData F X c) (t : ℝ) :
    deriv (xOf (ul3_T d)) t = (deriv F.γ t).1 :=
  ul1_deriv_xOf_liftT F.γ F.toSmoothLoop.differentiable c.τ (ul3_cstOf d) d.δ t

theorem ul3_deriv_zOf_T (d : ul3_LiftData F X c) (t : ℝ) :
    deriv (zOf (ul3_T d)) t = (deriv F.γ t).2 :=
  ul1_deriv_zOf_liftT F.γ F.toSmoothLoop.differentiable c.τ (ul3_cstOf d) d.δ t

/-- (L7) `z′ − y x′ > 0` -/
theorem ul3_T_positive (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) (t : ℝ) :
    0 < deriv (zOf (ul3_T d)) t - yOf (ul3_T d) t * deriv (xOf (ul3_T d)) t := by
  rw [ul3_deriv_xOf_T, ul3_deriv_zOf_T, ul3_yOf_T]
  exact ul2_liftY_admissible d.δ_pos (by linarith [d.δ_lt]) F.γ c.τ (ul3_cstOf d) d.gap d.adm t
    (ul1_liftY0_admissible F.γ t (F.regular t) (hdown t))

/-- the lift is embedded: equal points have equal projections, hence (after the reduction to the
fundamental period) are a twin pair of occurrences by `doubles`, where the heights `c_O ≠ c_U`
differ -/
theorem ul3_T_embedded (d : ul3_LiftData F X c) (s t : ℝ) (h : ul3_T d s = ul3_T d t) :
    SameT s t := by
  by_contra hne
  have hs := ul3_fract_mem s
  have ht := ul3_fract_mem t
  have hne' : Int.fract s ≠ Int.fract t := ul3_fract_ne_of_not_sameT hne
  have hper := ul3_T_periodic d
  have h' : ul3_T d (Int.fract s) = ul3_T d (Int.fract t) := by
    rw [← eq_of_sameT_of_periodic hper (ul3_sameT_fract s),
      ← eq_of_sameT_of_periodic hper (ul3_sameT_fract t)]
    exact h
  have hxz : F.γ (Int.fract s) = F.γ (Int.fract t) := by
    rw [← ul3_xzOf_T d]
    exact congrArg (fun p : Space => (p.1, p.2.2)) h'
  have hy : yOf (ul3_T d) (Int.fract s) = yOf (ul3_T d) (Int.fract t) :=
    congrArg (fun p : Space => p.2.1) h'
  obtain ⟨v, hv, hv'⟩ := c.doubles _ _ hs ht hne' hxz
  rw [hv, hv', ul3_yOf_T_tau, ul3_yOf_T_tau] at hy
  exact ul3_cst_ne_twin X d.cO d.cU d.lt v hy

/-- the double points of the projection are the finitely many twin pairs -/
theorem ul3_T_doubles_finite (d : ul3_LiftData F X c) :
    {q : ℝ × ℝ | q.1 ∈ Set.Ico (0 : ℝ) 1 ∧ q.2 ∈ Set.Ico (0 : ℝ) 1 ∧ q.1 ≠ q.2 ∧
      xzOf (ul3_T d) q.1 = xzOf (ul3_T d) q.2}.Finite := by
  apply (Set.finite_range fun v : X.Γ.Visit => (c.τ v, c.τ (X.twin v))).subset
  rintro ⟨s, t⟩ ⟨hs, ht, hne, heq⟩
  rw [ul3_xzOf_T] at heq
  obtain ⟨v, hv, hv'⟩ := c.doubles s t hs ht hne heq
  exact ⟨v, by rw [hv, hv']⟩

/-- transverse double points, from `RecordCarried.transverse` after the reduction to the
fundamental period -/
theorem ul3_T_transverse (d : ul3_LiftData F X c) (s t : ℝ) (hne : ¬ SameT s t)
    (heq : xzOf (ul3_T d) s = xzOf (ul3_T d) t) :
    det (deriv (xzOf (ul3_T d)) s) (deriv (xzOf (ul3_T d)) t) ≠ 0 := by
  rw [ul3_xzOf_T] at heq ⊢
  have hs := ul3_fract_mem s
  have ht := ul3_fract_mem t
  have hne' := ul3_fract_ne_of_not_sameT hne
  have e1 : F.γ s = F.γ (Int.fract s) := eq_of_sameT_of_periodic F.periodic (ul3_sameT_fract s)
  have e2 : F.γ t = F.γ (Int.fract t) := eq_of_sameT_of_periodic F.periodic (ul3_sameT_fract t)
  have d1 : deriv F.γ s = deriv F.γ (Int.fract s) :=
    eq_of_sameT_of_periodic F.toSmoothLoop.deriv_periodic (ul3_sameT_fract s)
  have d2 : deriv F.γ t = deriv F.γ (Int.fract t) :=
    eq_of_sameT_of_periodic F.toSmoothLoop.deriv_periodic (ul3_sameT_fract t)
  rw [e1, e2] at heq
  rw [d1, d2]
  obtain ⟨v, hv, hv'⟩ := c.doubles _ _ hs ht hne' heq
  rw [hv, hv']
  exact c.transverse v

/-- no triple point, from `RecordCarried.no_triple` -/
theorem ul3_T_no_triple (d : ul3_LiftData F X c) (r s t : ℝ) (hrs : ¬ SameT r s)
    (hst : ¬ SameT s t) (hrt : ¬ SameT r t) (h1 : xzOf (ul3_T d) r = xzOf (ul3_T d) s)
    (h2 : xzOf (ul3_T d) s = xzOf (ul3_T d) t) : False := by
  rw [ul3_xzOf_T] at h1 h2
  have er : F.γ r = F.γ (Int.fract r) := eq_of_sameT_of_periodic F.periodic (ul3_sameT_fract r)
  have es : F.γ s = F.γ (Int.fract s) := eq_of_sameT_of_periodic F.periodic (ul3_sameT_fract s)
  have et : F.γ t = F.γ (Int.fract t) := eq_of_sameT_of_periodic F.periodic (ul3_sameT_fract t)
  rw [er, es] at h1
  rw [es, et] at h2
  exact ul3_fract_ne_of_not_sameT hst
    (c.no_triple (ul3_fract_mem r) (ul3_fract_mem s) (ul3_fract_mem t)
      (ul3_fract_ne_of_not_sameT hrs) (ul3_fract_ne_of_not_sameT hrt) h1 (h1.trans h2))

/-- (L9) the transverse knot: the lift `liftT` with the fields of `TransverseKnot` -/
def ul3_knot (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c) :
    TransverseKnot where
  T := ul3_T d
  smooth := ul3_T_smooth hdown d
  periodic := ul3_T_periodic d
  embedded := ul3_T_embedded d
  positive := ul3_T_positive hdown d
  immersion := fun t => by rw [ul3_xzOf_T]; exact F.regular t
  doubles_finite := ul3_T_doubles_finite d
  transverse := ul3_T_transverse d
  no_triple := ul3_T_no_triple d

theorem ul3_knot_T (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c) :
    (ul3_knot hdown d).T = ul3_T d := rfl

/-- the front of the lift is the loop -/
theorem ul3_knot_xzOf (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) : xzOf (ul3_knot hdown d).T = F.γ :=
  ul3_xzOf_T d

end ul3_knot

/-! ##### (L10) the `HeightMarking` reading of `X` by the lift (FR-FL-C8) -/

section ul3_marking

variable {F : SmoothRegularLoop} {X : Diagram} {c : RecordCarried F X}

/-- the projection of the spatial knot is the loop -/
theorem ul3_projLoop_γ (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) (i : Fin 1) :
    ((ul3_knot hdown d).spatial.projLoop i).γ = F.γ :=
  ul3_xzOf_T d

/-- `(0, τ v)` is a crossing occurrence of the projection (its partner is `(0, τ (twin v))`) -/
theorem ul3_occ_mem (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (v : X.Γ.Visit) :
    ((0 : Fin 1), c.τ v) ∈ SmoothFront.occSetOf (ul3_knot hdown d).spatial.projLoop := by
  refine ⟨c.τ_mem v, ((0 : Fin 1), c.τ (X.twin v)), c.τ_mem _, ?_, ?_⟩
  · intro h
    have h' : c.τ v = c.τ (X.twin v) := congrArg Prod.snd h
    exact X.twin_ne v (c.τ_inj h').symm
  · show xzOf (ul3_T d) (c.τ v) = xzOf (ul3_T d) (c.τ (X.twin v))
    rw [ul3_xzOf_T]
    exact c.twin_eval v

/-- the occurrence of `X` as an occurrence of the projection -/
def ul3_occ (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (v : X.Γ.Visit) : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop :=
  ⟨((0 : Fin 1), c.τ v), ul3_occ_mem hdown d v⟩

theorem ul3_occ_injective (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) : Function.Injective (ul3_occ hdown d) := by
  intro v w h
  have h' : c.τ v = c.τ w :=
    congrArg (fun p : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop => p.1.2) h
  exact c.τ_inj h'

/-- every occurrence of the projection is realised: `doubles` -/
theorem ul3_occ_surjective (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) : Function.Surjective (ul3_occ hdown d) := by
  intro p
  obtain ⟨hp, q, hq, hne, heq⟩ := p.2
  have hne' : p.1.2 ≠ q.2 := fun h => hne (Prod.ext (Subsingleton.elim _ _) h)
  have heq' : F.γ p.1.2 = F.γ q.2 := by
    have h := heq
    rw [ul3_projLoop_γ, ul3_projLoop_γ] at h
    exact h
  obtain ⟨v, hv, -⟩ := c.doubles _ _ hp hq hne' heq'
  exact ⟨v, Subtype.ext (Prod.ext (Subsingleton.elim _ _) hv.symm)⟩

/-- the occurrence bijection `Φ` of the marking -/
def ul3_Φ (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c) :
    SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop ≃ X.Γ.Visit :=
  (Equiv.ofBijective (ul3_occ hdown d) ⟨ul3_occ_injective hdown d, ul3_occ_surjective hdown d⟩).symm

theorem ul3_occ_Φ (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (p : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop) :
    ul3_occ hdown d (ul3_Φ hdown d p) = p :=
  (Equiv.ofBijective (ul3_occ hdown d)
    ⟨ul3_occ_injective hdown d, ul3_occ_surjective hdown d⟩).apply_symm_apply p

/-- the parameter of an occurrence is `τ` of its image -/
theorem ul3_Φ_param (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (p : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop) :
    p.1.2 = c.τ (ul3_Φ hdown d p) := by
  have h := congrArg (fun q : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop => q.1.2)
    (ul3_occ_Φ hdown d p)
  exact h.symm

/-- the pairing: two distinct occurrences at one point are a twin pair (`doubles`) -/
theorem ul3_Φ_twin (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (p q : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop) (hne : p ≠ q)
    (heq : ((ul3_knot hdown d).spatial.projLoop p.1.1).γ p.1.2 =
      ((ul3_knot hdown d).spatial.projLoop q.1.1).γ q.1.2) :
    ul3_Φ hdown d q = X.twin (ul3_Φ hdown d p) := by
  have heq' : F.γ (c.τ (ul3_Φ hdown d p)) = F.γ (c.τ (ul3_Φ hdown d q)) := by
    rw [← ul3_Φ_param hdown d p, ← ul3_Φ_param hdown d q]
    have h := heq
    rw [ul3_projLoop_γ, ul3_projLoop_γ] at h
    exact h
  have hne' : c.τ (ul3_Φ hdown d p) ≠ c.τ (ul3_Φ hdown d q) := fun h =>
    hne ((ul3_Φ hdown d).injective (c.τ_inj h))
  obtain ⟨v, hv, hv'⟩ := c.doubles _ _ (c.τ_mem _) (c.τ_mem _) hne' heq'
  have hpv : ul3_Φ hdown d p = v := c.τ_inj hv
  have hqv : ul3_Φ hdown d q = X.twin v := c.τ_inj hv'
  rw [hqv, hpv]

/-- the height of an occurrence is the constant of its image (L8) -/
theorem ul3_height (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (p : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop) :
    (ul3_knot hdown d).spatial.height p.1 = ul3_cstOf d (ul3_Φ hdown d p) := by
  show yOf (ul3_T d) p.1.2 = _
  rw [ul3_Φ_param hdown d p]
  exact ul3_yOf_T_tau d _

/-- the smaller constant sits at the over occurrence (`cstOf` form) -/
theorem ul3_cstOf_lt_twin_iff (d : ul3_LiftData F X c) (v : X.Γ.Visit) :
    ul3_cstOf d v < ul3_cstOf d (X.twin v) ↔ X.overBit v = true :=
  ul3_cst_lt_twin_iff X d.cO d.cU d.lt v

/-- the smaller height sits at the over occurrence, the larger at the under one -/
theorem ul3_over_of_lt (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) (p q : SmoothFront.OccOf (ul3_knot hdown d).spatial.projLoop)
    (hne : p ≠ q)
    (heq : ((ul3_knot hdown d).spatial.projLoop p.1.1).γ p.1.2 =
      ((ul3_knot hdown d).spatial.projLoop q.1.1).γ q.1.2)
    (hlt : (ul3_knot hdown d).spatial.height p.1 < (ul3_knot hdown d).spatial.height q.1) :
    ∃ x : X.Γ.Crossing, ul3_Φ hdown d p = X.overVisit x ∧ ul3_Φ hdown d q = X.underVisit x := by
  have hq := ul3_Φ_twin hdown d p q hne heq
  rw [ul3_height, ul3_height, hq, ul3_cstOf_lt_twin_iff d] at hlt
  rcases X.visit_eq_over_or_under (ul3_Φ hdown d p) with h | h
  · refine ⟨(ul3_Φ hdown d p).1, h, ?_⟩
    rw [hq, h, Diagram.twin_overVisit, Diagram.overVisit_fst]
  · rw [h, Diagram.overBit_underVisit] at hlt
    exact absurd hlt Bool.false_ne_true

/-- the component bijection (one circle on each side) -/
def ul3_e (c : RecordCarried F X) : Fin 1 ≃ Fin X.Γ.c :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_fin, c.one])

/-- (L10) the reading: the polygon `X` carries the record of the lift's front with the smaller-`y`
over rule — `Φ` from `τ` (`twin_eval`, `doubles`, `τ_inj`), cyclic order from `order`, pairing from
`doubles`, over = smaller height from `c_O < c_U`, signs from `sign_eq` -/
def ul3_marking (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (hneg : ∀ x, X.sign x = -1)
    (d : ul3_LiftData F X c) :
    (ul3_knot hdown d).spatial.HeightMarking (ul3_knot hdown d).spatial.projLoop X where
  e := ul3_e c
  Φ := ul3_Φ hdown d
  comp_eq := fun p => by
    have h1 := (X.compOf (ul3_Φ hdown d p)).isLt
    have h2 := (ul3_e c p.1.1).isLt
    have h3 := c.one
    exact Fin.ext (by omega)
  between_iff := fun p q r _ _ => by
    rw [ul3_Φ_param hdown d p, ul3_Φ_param hdown d q, ul3_Φ_param hdown d r]
    exact c.order _ _ _
  pair_eq := fun p q hne heq => ul3_Φ_twin hdown d p q hne heq
  over_iff := fun p q hne heq => by
    rw [ul3_height, ul3_height, ul3_Φ_twin hdown d p q hne heq]
    exact (ul3_cstOf_lt_twin_iff d _).symm
  sgn_eq := fun p q hne heq hlt => by
    obtain ⟨x, hp, hq⟩ := ul3_over_of_lt hdown d p q hne heq hlt
    unfold SmoothFront.crossSignOf
    rw [ul3_projLoop_γ, ul3_projLoop_γ, ul3_Φ_param hdown d p, ul3_Φ_param hdown d q, hp, hq,
      Diagram.overVisit_fst, ite_eq_right (not_lt.mpr (ul3_det_neg c hneg x).le)]
    exact ul3_sign_cast hneg x

/-- the lift reads `X` -/
theorem ul3_reads (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (hneg : ∀ x, X.sign x = -1)
    (d : ul3_LiftData F X c) : (ul3_knot hdown d).Reads X :=
  ⟨ul3_marking hdown hneg d⟩

/-! ##### (L10) the front-writhe identity: `x ↦ (τ (overVisit x), τ (underVisit x))` is a bijection
onto `crossingPairs` -/

theorem ul3_front_eval (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) (t : ℝ) : (ul3_knot hdown d).front.eval t = F.γ t :=
  congrFun (ul3_xzOf_T d) t

theorem ul3_front_vel (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) (t : ℝ) : (ul3_knot hdown d).front.vel t = deriv F.γ t := by
  show deriv (xzOf (ul3_T d)) t = deriv F.γ t
  rw [ul3_xzOf_T]

/-- the front's crossing sign at the realised crossing `x` is `X`'s sign -/
theorem ul3_front_crossSign (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (hneg : ∀ x, X.sign x = -1) (d : ul3_LiftData F X c) (x : X.Γ.Crossing) :
    (ul3_knot hdown d).front.crossSign (c.τ (X.overVisit x)) (c.τ (X.underVisit x)) =
      (X.sign x : ℤ) := by
  unfold SmoothKnotDiagram.crossSign
  rw [ul3_front_vel, ul3_front_vel, ite_eq_right (not_lt.mpr (ul3_det_neg c hneg x).le),
    ul3_sign_cast hneg x]

/-- the realised crossing is an over-first crossing pair of the front -/
theorem ul3_pair_mem (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir) (d : ul3_LiftData F X c)
    (x : X.Γ.Crossing) :
    (c.τ (X.overVisit x), c.τ (X.underVisit x)) ∈ (ul3_knot hdown d).front.crossingPairs := by
  rw [SmoothKnotDiagram.mem_crossingPairs, SmoothKnotDiagram.mem_doubleSet]
  have hne : c.τ (X.overVisit x) ≠ c.τ (X.underVisit x) := fun h =>
    X.overVisit_ne_underVisit x (c.τ_inj h)
  have heq : (ul3_knot hdown d).front.eval (c.τ (X.overVisit x)) =
      (ul3_knot hdown d).front.eval (c.τ (X.underVisit x)) := by
    rw [ul3_front_eval, ul3_front_eval]
    exact c.twin_eval (X.overVisit x)
  refine ⟨⟨c.τ_mem _, c.τ_mem _, hne, heq⟩, ?_⟩
  rw [TransverseKnot.front_isOver]
  refine ⟨⟨fun h => hne (SameT.eq_of_mem_Ico (c.τ_mem _) (c.τ_mem _) h), heq⟩, ?_⟩
  show yOf (ul3_T d) _ < yOf (ul3_T d) _
  rw [ul3_yOf_T_tau, ul3_yOf_T_tau]
  exact (ul3_cstOf_lt_twin_iff d (X.overVisit x)).mpr (X.overBit_overVisit x)

/-- every crossing pair of the front is a realised crossing -/
theorem ul3_crossingPairs_surj (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (d : ul3_LiftData F X c) (q : ℝ × ℝ) (hq : q ∈ (ul3_knot hdown d).front.crossingPairs) :
    ∃ x : X.Γ.Crossing, (c.τ (X.overVisit x), c.τ (X.underVisit x)) = q := by
  rw [SmoothKnotDiagram.mem_crossingPairs, SmoothKnotDiagram.mem_doubleSet] at hq
  obtain ⟨⟨h1, h2, hne, heq⟩, hover⟩ := hq
  rw [ul3_front_eval, ul3_front_eval] at heq
  obtain ⟨v, hv, hv'⟩ := c.doubles _ _ h1 h2 hne heq
  rw [TransverseKnot.front_isOver] at hover
  have hy : yOf (ul3_T d) q.1 < yOf (ul3_T d) q.2 := hover.2
  rw [hv, hv', ul3_yOf_T_tau, ul3_yOf_T_tau, ul3_cstOf_lt_twin_iff d] at hy
  rcases X.visit_eq_over_or_under v with h | h
  · refine ⟨v.1, Prod.ext ?_ ?_⟩
    · show c.τ (X.overVisit v.1) = q.1
      rw [hv]
      exact congrArg c.τ h.symm
    · show c.τ (X.underVisit v.1) = q.2
      rw [hv']
      exact congrArg c.τ ((X.twin_overVisit v.1).symm.trans (congrArg X.twin h.symm))
  · rw [h, Diagram.overBit_underVisit] at hy
    exact absurd hy Bool.false_ne_true

/-- (L10) the front's writhe is `X`'s -/
theorem ul3_front_writhe (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (hneg : ∀ x, X.sign x = -1) (d : ul3_LiftData F X c) :
    (ul3_knot hdown d).front.writhe = X.writhe := by
  unfold SmoothKnotDiagram.writhe Diagram.writhe
  symm
  refine Finset.sum_nbij (fun x => (c.τ (X.overVisit x), c.τ (X.underVisit x))) ?_ ?_ ?_ ?_
  · intro x _
    exact ul3_pair_mem hdown d x
  · intro x _ y _ h
    have h' : c.τ (X.overVisit x) = c.τ (X.overVisit y) := congrArg Prod.fst h
    exact congrArg (fun v : X.Γ.Visit => v.1) (c.τ_inj h')
  · intro q hq
    obtain ⟨x, hx⟩ := ul3_crossingPairs_surj hdown d q hq
    exact ⟨x, Finset.mem_univ x, hx⟩
  · intro x _
    exact (ul3_front_crossSign hdown hneg d x).symm

end ul3_marking


/-- (U-LIFT-3) the transverse lift: a regular loop with no downward vertical tangency carrying an
all-negative diagram `X` lifts to a positive transverse knot whose front is the loop, which reads `X`
(the smaller-`y` over rule realising `X`'s over data: a `HeightMarking` of `K.spatial.projLoop`),
and whose front's writhe is `X`'s -/
theorem ulift_exists_transverse_lift (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X)
    (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ downDir)
    (hneg : ∀ x, X.sign x = -1) :
    ∃ K : TransverseKnot, xzOf K.T = F.γ ∧ K.Reads X ∧ K.front.writhe = X.writhe := by
  obtain ⟨d⟩ := ul3_exists_liftData F X c hdown hneg
  exact ⟨ul3_knot hdown d, ul3_knot_xzOf hdown d, ul3_reads hdown hneg d,
    ul3_front_writhe hdown hneg d⟩

/-! ### 8.8 Unit U-C: the assembly of clause (C) (sm-3:4417-4575) with the row-94 bound as hypothesis -/

/-- (U-C helper) `supp (zZeroPart f) ⊆ supp f` (`coeffAt_zZeroPart_zero/of_ne`): the attained minimal
`a`-exponent of the `z⁰` row is an exponent of `f`, so `mindegAZ f ≤ mindegAZ (zZeroPart f)`
(`mindegAZ_spec` twice) -/
theorem uc_mindegAZ_le_zZeroPart (f : R) (hf : f ≠ 0) (hz : zZeroPart f ≠ 0) :
    mindegAZ f ≤ mindegAZ (zZeroPart f) := by
  obtain ⟨⟨k, hk⟩, -⟩ := mindegAZ_spec hz
  by_cases hk0 : k = 0
  · subst hk0
    rw [coeffAt_zZeroPart_zero] at hk
    exact (mindegAZ_spec hf).2 _ _ hk
  · exact absurd (coeffAt_zZeroPart_of_ne f _ k hk0) hk

/-- (U-C helper) the chain of PLAN_FINAL.md §3 (C) steps 2-7 on a polygon already in the normalised
orientation (`AllPosOrOneNeg C.P`), for any polygon diagram `Db` whose accepted diagram is `D̄ =
X.switchAll`: (B) (`ub_exists_admissibleDirection`, `ub_tangencyCount_of_admissible` at `ε := ε₀/2`),
`R := |rot| ∈ ℕ` (`rotationNumber_integer`), the curls (`ucurl_exists_curled`), the rotation
(`urot_exists_rotated`), the transverse lift (`ulift_exists_transverse_lift`), the row-94 bound
`hbound`, then `−w − R ≤ −degAZ (ι (P X)) − 1 = mindegAZ (P X) − 1` (`usw_P_switchAll`,
`ui_mirrorSubstitution.degAZ_eq`, `P_ne_zero`), cast to `ℝ` -/
theorem uc_floor_of_allPos (hbound : TransverseFrontBound) (C : PolyComp) (X : Diagram)
    (h : CarrierFloorCHyp C X) (hpos : AllPosOrOneNeg C.P) (Db : PolygonDiagram C)
    (hD : Db.toDiagram = X.switchAll) :
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ) := by
  -- (B): the admissible direction and the admissible `ε := ε₀/2`
  obtain ⟨u, hu⟩ := ub_exists_admissibleDirection C h.turn_exists h.turn_ne hpos
  have hclear : 0 < CornerRounding.clearance C := CornerRounding.clearance_pos h.generic
  set ε : ℝ := CornerRounding.clearance C / 2 with hε
  have hadm : CornerRounding.Admissible C Db ε :=
    ⟨h.turn_ne, by rw [hε]; positivity, by rw [hε]; linarith⟩
  have hcount := (ub_tangencyCount_of_admissible C Db h.turn_ne hpos u hu ε hadm).1
  -- `R := |rot|` as a natural number (lem:rot: `rot ∈ ℤ`)
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ((R : ℕ) : ℝ) = |rotationNumber C.P| := by
    obtain ⟨k, hk⟩ := rotationNumber_integer h.turn_exists
    exact ⟨k.natAbs, by rw [hk, Nat.cast_natAbs, Int.cast_abs]⟩
  rw [← hR] at hcount
  -- `D̄` is all-negative (`usw_switchAll_sign`, every crossing of `X` positive)
  have hneg : ∀ x, Db.toDiagram.sign x = -1 := by
    rw [hD]
    intro x
    have e : X.switchAll.sign x = -X.sign x := usw_switchAll_sign X x
    rw [e, (Link.Diagram.isPositive_iff_sign_eq_one X x).mp (h.positive x)]
  -- the `R` curls (cf:lem-curl)
  obtain ⟨F', X', ⟨c⟩, hnou, hP, hw, hneg'⟩ :=
    ucurl_exists_curled C Db ε hadm u hu.1 R hcount hneg
  -- rotate so that `u` is the downward vertical
  obtain ⟨φ, G, -, ⟨c'⟩, hiff⟩ := urot_exists_rotated F' X' c u hu.1
  have hdown : ∀ t, SM.normalize (deriv G.γ t) ≠ downDir := fun t ht => hnou t ((hiff t).mp ht)
  -- the transverse lift, read by row 94
  obtain ⟨K, -, hread, hwr⟩ := ulift_exists_transverse_lift G X' c' hdown hneg'
  have hb := hbound K X' hread
  -- the degree algebra: `P X_R = P D̄ = ι (P X)`, `degAZ (ι (P X)) = −mindegAZ (P X)`, `w(X_R) = −w − R`
  have hPX' : P X' = iotaHom (P X) := by rw [hP, hD, usw_P_switchAll]
  have hdeg : degAZ (iotaHom (P X)) = -mindegAZ (P X) :=
    ui_mirrorSubstitution.degAZ_eq (P X) (P_ne_zero X)
  have hw' : X'.writhe = -X.writhe - R := by rw [hw, hD, usw_switchAll_writhe]
  rw [hwr, hw', hPX', hdeg] at hb
  have hZ : (1 - X.writhe - (R : ℤ) : ℤ) ≤ mindegAZ (P X) := by linarith
  have hZR : ((1 - X.writhe : ℤ) : ℝ) - ((R : ℕ) : ℝ) ≤ (mindegAZ (P X) : ℝ) := by
    exact_mod_cast hZ
  rw [hR] at hZR
  exact hZR

/-- (U-C helper) step 1, the transport of the hypotheses of clause (C) to the reversed pair
`(−L, −D)` when the alternative holds for `reversal C.P`: the shadow is the reversed single polygon
(`X.reverse.Γ = X.Γ.reverseShadow`, definitionally), crossing signs are kept (`reverse_sign`), the
principal turns negate (`principalTurn_reversal`); the redundant fields via `CarrierFloorCHyp.of_diagram` -/
theorem uc_carrierFloorCHyp_reverse (C : PolyComp) (X : Diagram) (h : CarrierFloorCHyp C X)
    (hpos : AllPosOrOneNeg (reversal C.P)) : CarrierFloorCHyp C.reverse X.reverse := by
  refine CarrierFloorCHyp.of_diagram C.reverse X.reverse ?_ ?_ ?_ (Or.inl hpos)
  · show X.Γ.reverseShadow = _
    rw [h.shadow]
  · intro x
    have e : X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x) := Link.Diagram.reverse_sign X x
    rw [Link.Diagram.isPositive_iff_sign_eq_one, e]
    exact (Link.Diagram.isPositive_iff_sign_eq_one X _).mp (h.positive _)
  · intro i
    have e : principalTurn C.reverse.P i = -principalTurn C.P (2 - i) :=
      principalTurn_reversal h.turn_exists i
    rw [e]
    exact neg_ne_zero.mpr (h.turn_ne _)

/-- (U-C helper) cf:eq-floor: normalise by (R) — WLOG `AllPosOrOneNeg C.P`, otherwise pass to
`(C.reverse, X.reverse)` (`P` kept by `ur_P_reverse_all`, the writhe by `reverse_writhe`, `|rot|` by
`rotationNumber_reversal`) — then the chain on `D̄ := PolygonDiagram.ofDiagram X.switchAll`
(`toDiagram_ofDiagram`) -/
theorem uc_floor (hbound : TransverseFrontBound) (C : PolyComp) (X : Diagram)
    (h : CarrierFloorCHyp C X) :
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ) := by
  rcases h.alternative with hpos | hpos
  · exact uc_floor_of_allPos hbound C X h hpos (PolygonDiagram.ofDiagram X.switchAll h.shadow)
      (PolygonDiagram.toDiagram_ofDiagram _ _)
  · have h' := uc_carrierFloorCHyp_reverse C X h hpos
    have hmain := uc_floor_of_allPos hbound C.reverse X.reverse h' hpos
      (PolygonDiagram.ofDiagram X.reverse.switchAll h'.shadow)
      (PolygonDiagram.toDiagram_ofDiagram _ _)
    have e : rotationNumber C.reverse.P = -rotationNumber C.P := rotationNumber_reversal h.turn_exists
    rw [ur_P_reverse_all, Link.Diagram.reverse_writhe, e, abs_neg] at hmain
    exact hmain

/-- normalise by (R) (WLOG `AllPosOrOneNeg C.P`), `D̄ := X.switchAll` on `PolygonDiagram.ofDiagram`,
(B) at `ε := ε₁/2`, `ucurl_exists_curled` with `R := rot`, `urot_exists_rotated`,
`ulift_exists_transverse_lift`, `hbound K X_R`, then the degree algebra
`−w − R ≤ −degAZ (P X_R) − 1 = −degAZ (ι (P X)) − 1 = mindegAZ (P X) − 1` (`usw_P_switchAll`,
`ui_mirrorSubstitution.degAZ_eq`, `P_ne_zero`), cast to `ℝ` with `R = |rot|`; `floor_zZero` by
`supp (zZeroPart f) ⊆ supp f` and `mindegAZ_spec` -/
theorem cf_thm_carrierfloor_C_of_bound (hbound : TransverseFrontBound) : CarrierFloorCData := by
  -- (U-C) `floor` is `uc_floor`; `floor_zZero` from it and `mindegAZ (P X) ≤ mindegAZ (zZeroPart (P X))`
  -- (`uc_mindegAZ_le_zZeroPart`, `P_ne_zero`)
  refine ⟨fun C X h => uc_floor hbound C X h, fun C X h hz => ?_⟩
  have h1 := uc_floor hbound C X h
  have h2 : (mindegAZ (P X) : ℝ) ≤ (mindegAZ (zZeroPart (P X)) : ℝ) := by
    exact_mod_cast uc_mindegAZ_le_zZeroPart (P X) (P_ne_zero X) hz
  linarith

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

/-- (U-F helper) "either all turns are left, or exactly one turn is right" on a regular polygon
gives clause (C)'s "either all principal turns are positive, or exactly one is negative and all
others are positive": `turn = sign (principalTurn)` on the regular locus (`principalTurn_sign`,
lem:uniformrot's reading of def:chirotope). -/
theorem uf_allPosOrOneNeg_of_allLeftOrOneRight {m : ℕ} [NeZero m] (Q : LabelledTuple m)
    (hreg : Regular Q) (h : AllLeftOrOneRight Q) : AllPosOrOneNeg Q := by
  rcases h with h | ⟨j₀, hj₀, hj⟩
  · exact Or.inl fun i => principalTurn_pos_of_left hreg (h i)
  · refine Or.inr ⟨j₀, ?_, fun j hj' => principalTurn_pos_of_left hreg (hj j hj')⟩
    exact sign_eq_neg_one_iff.mp ((principalTurn_sign hreg j₀).trans hj₀)

/-- (U-F helper) thm:floor's alternative on the corner polygon `Q` or its reversal is clause (C)'s
`UniformOrOneDissent` on `carrierPolyComp` (whose polygon is `ccpCornerPolygon`, definitionally);
regularity of `Q` is lem:carriers (ii) (`ccpCornerPolygon_regular`), of `reversal Q` its transport
(`regular_reversal_forward`). -/
theorem uf_uniformOrOneDissent_of_carrier (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (halt : CarrierUniformOrOneDissent hn hP S q) :
    UniformOrOneDissent (carrierPolyComp hn hP S q hS) := by
  have hreg : Regular (ccpCornerPolygon hn hP S q) := ccpCornerPolygon_regular hn hP hS q
  rcases halt with h | h
  · exact Or.inl (uf_allPosOrOneNeg_of_allLeftOrOneRight _ hreg h)
  · exact Or.inr (uf_allPosOrOneNeg_of_allLeftOrOneRight _ (regular_reversal_forward hreg) h)

/-- (U-F helper) the principal turns of the carrier polygon are nonzero: lem:carriers (ii)
"all corner turns are nonzero" (`ccpCornerPolygon_turn_ne_zero`) read through
`turn = sign (principalTurn)` (`principalTurn_sign`). -/
theorem uf_carrier_principalTurn_ne_zero (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (i : ZMod (ccpCornerCount hn hP S q)) :
    principalTurn (carrierPolyComp hn hP S q hS).P i ≠ 0 := by
  intro h
  apply ccpCornerPolygon_turn_ne_zero hn hP hS q i
  rw [← principalTurn_sign (ccpCornerPolygon_regular hn hP hS q) i]
  show SignType.sign (principalTurn (ccpCornerPolygon hn hP S q) i) = 0
  rw [h]
  exact sign_zero

/-- (U-F helper) the hypotheses of clause (C) for the positive lift of a carrier: `shadow` is
`positiveLift_Γ` (`rfl`), positivity is def:positive-lift (`positiveLift_isPositive`), nonzero
turns are lem:carriers (ii), the alternative is thm:floor's; the redundant printed hypotheses come
from the accepted diagram (`CarrierFloorCHyp.of_diagram`; the "no corner on a non-incident edge"
clause is `ccpCornerPolygon_tail_off` inside `carrierShadow_generic`). -/
theorem uf_carrierFloorCHyp (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (halt : CarrierUniformOrOneDissent hn hP S q) :
    CarrierFloorCHyp (carrierPolyComp hn hP S q hS) (positiveLift hn hP S q hS) :=
  CarrierFloorCHyp.of_diagram _ _ rfl (positiveLift_isPositive hn hP S q hS)
    (uf_carrier_principalTurn_ne_zero hn P hP S hS q)
    (uf_uniformOrOneDissent_of_carrier hn P hP S hS q halt)

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
  -- clause (C) on `C := carrierPolyComp`, `X := positiveLift`
  have hfloor := hC.floor _ _ (uf_carrierFloorCHyp hn P hP S hS q halt)
  -- `w = m_Q`, `P = homfly` (so `P X = cornerHomfly` definitionally), `rot C.P = carrierRotation` (rfl)
  rw [positiveLift_writhe_eq_carrierCrossingCount hn hP S q hS, P_eq_homfly] at hfloor
  change ((1 - (carrierCrossingCount hn hP S q : ℤ) : ℤ) : ℝ) - |carrierRotation hn hP S q| ≤
    (mindegAZ (cornerHomfly hn hP S q hS) : ℝ) at hfloor
  have hreal : 1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤
      (mindegAZ (cornerHomfly hn hP S q hS) : ℝ) := by
    have e : ((1 - (carrierCrossingCount hn hP S q : ℤ) : ℤ) : ℝ) =
        1 - (carrierCrossingCount hn hP S q : ℝ) := by
      rw [Int.cast_sub, Int.cast_one, Int.cast_natCast]
    rw [e] at hfloor
    exact hfloor
  refine ⟨?_, hreal⟩
  -- the ℤ form through the printed equality `d_Q = 1 − m_Q − |r_Q|` (`cornerSlot_cast`)
  have hZ : ((cornerSlot hn hP S q : ℤ) : ℝ) ≤ (mindegAZ (cornerHomfly hn hP S q hS) : ℝ) := by
    rw [cornerSlot_cast hn hP hS q]
    exact hreal
  exact_mod_cast hZ

/-- the `z`-parity clause from lp:core's knot support (`P_support` with `positiveLift_componentCount = 1`,
`P_eq_homfly`, `mindegZZ_spec`) — provable now -/
theorem uf_z_parity (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    InSupportM 1 (cornerHomfly hn hP S q hS) ∧ 0 ≤ mindegZZ (cornerHomfly hn hP S q hS) := by
  -- `cornerHomfly = homfly (positiveLift …) = P (positiveLift …)` (lp:coefficient-transport)
  have hPX : SM.P (positiveLift hn hP S q hS) = cornerHomfly hn hP S q hS := P_eq_homfly _
  rw [← hPX]
  -- `InSupportM 1`: lp:support with `componentCount = 1` (definitionally)
  refine ⟨P_support _, ?_⟩
  -- `0 ≤ mindeg_z`: the attained minimal `z`-exponent is `2j` by lp:core's knot clause
  obtain ⟨d, hd⟩ := (mindegZZ_spec (P_ne_zero (positiveLift hn hP S q hS))).1
  obtain ⟨j, hj⟩ := P_knot_support _ (positiveLift_componentCount hn hP S q hS) d _ hd
  rw [hj]
  positivity

/-- thm:floor from clause (C) (proposed row name `SM.thm_floor`, assembled once row 94 lands) -/
theorem thm_floor_of_C (hC : CarrierFloorCData) : FloorTheoremData where
  a_floor := fun hn P hP S hS q halt => uf_a_floor_of_C hC hn P hP S hS q halt
  z_parity := fun hn P hP S hS q => uf_z_parity hn P hP S hS q

theorem thm_floor_of_bound (hbound : TransverseFrontBound) : FloorTheoremData :=
  thm_floor_of_C (cf_thm_carrierfloor_C_of_bound hbound)

end Floor

/-! ## 9. The row-94 hypothesis discharged (the accepted `SM.fd_contact`, SM/FdContactUnits.lean) -/

/-- The two displays of fd:contact for the document's `SM.sl`, read off the accepted row theorem. -/
theorem fdContactShape_sl : FdContactShape SM.sl where
  front_writhe := fd_contact.front_writhe
  representative_bound := fun K X hX => by
    have h := fd_contact.representative_bound K X hX
    exact_mod_cast h

/-- The writhe bound of row 94 in its sl-free form, unconditionally. -/
theorem transverseFrontBound : TransverseFrontBound :=
  transverseFrontBound_of_fdContactShape fdContactShape_sl

end

end SM
