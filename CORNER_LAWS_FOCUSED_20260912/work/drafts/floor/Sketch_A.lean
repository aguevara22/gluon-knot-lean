import SM.Curl
import SM.TransverseFront
import SM.CornerStateSum
import SM.LinkPositiveLift
import SM.UniformRotation

/-! # Rows 99 cf:thm-carrierfloor and 100 thm:floor — design sketch A (fidelity-first), 2026-09-15

Companion of work/drafts/floor/DESIGN_A.md.  Check: `cd work/lean && lake env lean ../drafts/floor/Sketch_A.lean`.
Statement text (§1-§6, §8) has NO sorry; the proof route (§7, §9) is stated as leaves with `sorry`
(design sketch, not a proof).  Nothing here is to be ported without the row's statement review.

Sources: reference/SM/sm-3-statesum.tex:4282-4339 (row 99 statement), 4340-4575 (proof),
4576-4585 (row 100 statement), 4586-4602 (proof).  Accepted inputs (work/lean): SM/Rounding.lean
(cf:lem-rounding, `RoundingWitness`, `Carried`, `CornerRounding.roundedWitness/clearance/Admissible`),
SM/Curl.lean (cf:lem-curl, `RecordCarried`, `CurlSite`, `CurlWitness`), SM/TurningNumber.lean +
SM/TurnLift.lean (`ClosedC1Curve.rot`, `rot_reverse`), SM/RotationTheorem.lean (lem:rot),
SM/UniformRotation.lean (lem:uniformrot), SM/LinkDiagram.lean + SM/LinkMoves.lean (`Diagram.reverse`,
`reverse_sign`, `reverse_writhe`, `ReverseCarries`, `IsSkeinTriple.reverse`), SM/PolynomialBlock.lean
(lp:core, rp:record-polynomial), SM/CoefficientTransport.lean, SM/TransverseFront.lean
(`TransverseKnot`, `SmoothKnotDiagram`), SM/CornerStateSum.lean (def:C), SM/LinkPositiveLift.lean,
SM/CarriersLemma.lean. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. Assumed interface — to be unified with the contact lane (row 94)

`SmoothKnotDiagram.Carries` is copied from work/drafts/gap2/Gap2Statements.lean §1 (record-level
carrying of a polygonal one-component `Diagram` by a smooth knot diagram; over = the diagram's own
`isOver`).  The contact lane fixes its final form; the (C) route below depends on it staying
RECORD-LEVEL (no clause tying the polygon's crossing points to the front's double points), see
DESIGN_A.md §3(C) step 5. -/

/-- record-level carrying of the polygonal one-component diagram `X` by the smooth knot diagram `D` -/
structure SmoothKnotDiagram.Carries (D : SmoothKnotDiagram) (X : Diagram) where
  one : X.Γ.c = 1
  τ : X.Γ.Visit → ℝ
  τ_mem : ∀ v, τ v ∈ Set.Ico (0 : ℝ) 1
  τ_inj : Function.Injective τ
  twin_double : ∀ v, D.IsDouble (τ v) (τ (X.twin v))
  doubles : ∀ s t : ℝ, s ∈ Set.Ico (0 : ℝ) 1 → t ∈ Set.Ico (0 : ℝ) 1 → D.IsDouble s t →
    ∃ v : X.Γ.Visit, s = τ v ∧ t = τ (X.twin v)
  order : ∀ v w z : X.Γ.Visit,
    (cycBetween (τ v) (τ w) (τ z) ↔ cycBetween (X.visitCoord v) (X.visitCoord w) (X.visitCoord z))
  over_eq : ∀ x : X.Γ.Crossing, D.isOver (τ (X.overVisit x)) (τ (X.underVisit x))
  sign_eq : ∀ x : X.Γ.Crossing,
    (X.sign x : ℤ) = D.crossSign (τ (X.overVisit x)) (τ (X.underVisit x))

/-- The writhe bound of row 94 fd:contact in its sl-free form (the memo's
`TransverseFrontBoundData.writhe_bound`), taken as an EXPLICIT HYPOTHESIS by the (C) route:
"for every transverse knot K and every polygonal diagram X carrying its front,
`writhe(front) ≤ −max deg_a P_X − 1`". -/
def TransverseFrontBound : Prop :=
  ∀ (K : TransverseKnot) (X : Diagram), K.front.Carries X → K.front.writhe ≤ -degAZ (P X) - 1

/-! ## 2. Clause (R) (sm-3:4283-4290) -/

/-- Clause (R), one field per printed sentence.  "Here rot is as in Lemma lem:rot for polygons and
Definition cf:def-turning for the underlying plane curve of a smooth diagram" scopes the last
sentence, which therefore has a polygon field and a `C¹`-curve field. -/
structure CarrierFloorRData : Prop where
  /-- "Let D be an oriented knot diagram and −D the same diagram with every arrow reversed.
  Then P_{−D} = P_D" -/
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
  directions and by the transition profile, which is fixed once and for all" -/
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

/-- "has exactly R points at which its unit tangent equals u …; at each of them the tangent crosses
that direction in the positive sense": the parameters of the fundamental period with tangent `u`
form a finite set of cardinality `R`, and each lies inside a junction `(a j, b j)` where the
junction lift `θ j` of the tangent (cf:lem-rounding (b)) has positive derivative -/
def TangencyCount {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (u : Plane) (R : ℝ) : Prop :=
  {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}.Finite ∧
  (({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}.ncard : ℝ) = R) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) 1, W.T t = u →
    ∃ j, j < C.k ∧ t ∈ Set.Ioo (W.a j) (W.b j) ∧ 0 < deriv (W.θ j) t

/-- "there are a direction u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁) the rounded curve L_ε
of the record Round(L, D, ε) from clause (A) has exactly R points at which its unit tangent equals u
and exactly R at which it equals −u; at each of them the tangent crosses that direction in the
positive sense", `R = |rot(L)|`.  `ε₁ ≤ ε₀(L)` so that the record exists at every such `ε`
(the printed proof takes `ε₁ = ε₀(L)`); the admissibility proof `h` exists under the row's
nonzero-turn hypothesis and is irrelevant (`one_record`). -/
def BClaim (C : PolyComp) (D : PolygonDiagram C) : Prop :=
  ∃ (u : Plane) (ε₁ : ℝ), euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ CornerRounding.clearance C ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ h : CornerRounding.Admissible C D ε,
      TangencyCount (Round C D ε h) u |rotationNumber C.P| ∧
      TangencyCount (Round C D ε h) (-u) |rotationNumber C.P|

/-- Clause (B).  "Let L be a closed polygon with nonzero edges and nonzero principal turns, finitely
many transverse double points, no triple points, no corner at a double point and no corner on a
non-incident edge, carrying a diagram D" = `C : PolyComp`, `D : PolygonDiagram C` (its `generic`
field is that list) and `∀ i, principalTurn C.P i ≠ 0`.  The claim is made for the polygon in the
normalised orientation ("after reversing orientation if necessary … perform the allowed
normalization once", sm-3:4368-4370): for `L` itself when `L` is already uniform / one-dissent, for
`−L` (carrying `−D`) otherwise (FR-FL-B1). -/
structure CarrierFloorBData : Prop where
  tangencies : ∀ (C : PolyComp) (D : PolygonDiagram C), (∀ i, principalTurn C.P i ≠ 0) →
    UniformOrOneDissent C →
    (AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)

/-! ## 5. Clause (C) (sm-3:4319-4337): the floor -/

/-- The hypotheses of clause (C), one field per printed clause (sm-3:4320-4333), on the oriented
knot diagram `X` whose underlying plane curve is the polygon `L = C.P`.  The three redundant fields
(`turn_exists`, `turn_lt_pi`, `generic`) are printed and kept; they follow from `shadow` and
`X.generic` (`CarrierFloorCHyp.of_diagram`). -/
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
def:adeg's `mindeg_a` applies to it): the monomials `a^d z^0` of `f`. -/
def zZeroPart (f : R) : R :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun e : ℤ × ℤ => e.2 = 0) f.coeff)

theorem coeffAt_zZeroPart_zero (f : R) (d : ℤ) : coeffAt d 0 (zZeroPart f) = coeffAt d 0 f := by
  simp [zZeroPart, coeffAt]

theorem coeffAt_zZeroPart_of_ne (f : R) (d k : ℤ) (hk : k ≠ 0) : coeffAt d k (zZeroPart f) = 0 := by
  simp [zZeroPart, coeffAt, hk]

/-- Clause (C): "Then mindeg_a P_D(a,z) ≥ 1 − w − R [cf:eq-floor], and the same bound holds for
f_D(a) = [z⁰]P_D(a,z) whenever f_D ≠ 0", `w = X.writhe`, `R = |rot(L)|`. -/
structure CarrierFloorCData : Prop where
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  floor_zZero : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X → zZeroPart (P X) ≠ 0 →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (zZeroPart (P X)) : ℝ)

/-! ## 6. The row bundle (proposed name `SM.cf_thm_carrierfloor : CarrierFloorData`; no fixed name in
work/lean/axiom-policy.json) -/

/-- cf:thm-carrierfloor: the four printed clauses. -/
structure CarrierFloorData : Prop where
  clauseR : CarrierFloorRData
  clauseA : CarrierFloorAData
  clauseB : CarrierFloorBData
  clauseC : CarrierFloorCData

/-! ## 7. Proof route (leaves as `sorry`; unit prefixes in DESIGN_A.md §5) -/

/-! ### 7.1 Unit U-R: reversal (lp:coefficient-transport + `ReverseCarries` + `IsSkeinTriple.reverse`) -/

/-- `D ↦ P_{−D}` is an `RCompetitor` (accepted `reverseCarries_linkEquiv` pieces + `reverse_skein`
+ the crossing-free circle is carried); hence `P X.reverse = P X` for EVERY link diagram (the
printed proof argues "on all oriented link diagrams"; the row states the knot case). -/
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

/-! ### 7.2 Unit U-A: definitional properties of the accepted construction -/

theorem cf_thm_carrierfloor_A : CarrierFloorAData where
  one_record := fun _ _ _ _ _ => rfl
  one_curve := fun _ _ _ _ => rfl
  one_diagram := fun _ D _ h => ⟨⟨(Round _ D _ h).carried⟩, (Round _ D _ h).same_writhe⟩
  junction_determined := by
    sorry
  length_determined := by
    sorry
  rest_is_L := fun _ _ _ h => ⟨(Round _ _ _ h).outside, (Round _ _ _ h).straight⟩

/-! ### 7.3 Unit U-B: the tangency count (library form with the direction as a parameter, then the row) -/

/-- the printed choice of `u` (sm-3:4372-4376): a unit direction, neither it nor its antipode an edge
direction, and neither in the closed swept arc of any negative turn -/
def AdmissibleDirection (C : PolyComp) (u : Plane) : Prop :=
  euclideanLength u = 1 ∧
  (∀ i : ZMod C.k, SM.normalize (edge C.P i) ≠ u ∧ SM.normalize (edge C.P i) ≠ -u) ∧
  ∀ j : ZMod C.k, principalTurn C.P j < 0 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
    CornerRounding.dirOf ((planeComplex (CornerRounding.uDir C j)).arg + s * principalTurn C.P j) ≠ u ∧
    CornerRounding.dirOf ((planeComplex (CornerRounding.uDir C j)).arg + s * principalTurn C.P j) ≠ -u

/-- (B-strong) for every admissible direction and every admissible `ε` (the printed proof, with
`ε₁ = ε₀(L)`): the count `⌊x + R⌋ − ⌊x⌋ = R` from the concatenated lift, jumps only in increasing
junctions. -/
theorem ub_tangencyCount_of_admissible (C : PolyComp) (D : PolygonDiagram C)
    (hturn : ∀ i, principalTurn C.P i ≠ 0) (hpos : AllPosOrOneNeg C.P) (u : Plane)
    (hu : AdmissibleDirection C u) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    TangencyCount (Round C D ε h) u |rotationNumber C.P| ∧
    TangencyCount (Round C D ε h) (-u) |rotationNumber C.P| := by
  sorry

/-- "Such u exists" (sm-3:4374-4376): the forbidden set is finite together with a closed arc of
length `< 2π`. -/
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

/-! ### 7.4 Units of clause (C): the crossing switch, the ring involution, the curls, the rotation,
the transverse lift, the assembly -/

/-- `D̄`: "the diagram with every crossing switched" (sm-3:4431, 4533) — same shadow, over ↦ under -/
def Link.Diagram.switchAll (D : Diagram) : Diagram := D.withOver D.underStrand D.under_mem

/-- the involutive automorphism `ι : (a, z) ↦ (a⁻¹, −z)` of `R` (sm-3:4540), as the `ℤ`-algebra
homomorphism sending the generators to the units `a⁻¹`, `−z` -/
def iotaHom : R →ₐ[ℤ] R :=
  AddMonoidAlgebra.lift ℤ R (ℤ × ℤ) (unitPowers (R.aUnit⁻¹) (-R.zUnit))

/-- (U-SW) the mirror identity `P_{D̄}(a, z) = P_D(a⁻¹, −z)` (sm-3:4533-4551): `D ↦ ι(P_{D̄})` is an
`RCompetitor` — needs the switch-all transport of the four generators and of skein triples with
`D₊`, `D₋` exchanged (NEW; the accepted `MirrorCarries` is the reflection, DESIGN_A.md FR-FL-C4). -/
theorem usw_P_switchAll (X : Diagram) : P X.switchAll = iotaHom (P X) := by
  sorry

/-- (U-ι) "the substitution negates every a-exponent and cannot cancel a nonzero extreme coefficient":
`max deg_a ι(f) = −mindeg_a f` for `f ≠ 0`. -/
theorem ui_degAZ_iotaHom (f : R) (hf : f ≠ 0) : degAZ (iotaHom f) = -mindegAZ f := by
  sorry

/-- the rotation of the plane by the angle `φ` -/
def rotationMap (φ : ℝ) (p : Plane) : Plane :=
  (Real.cos φ * p.1 - Real.sin φ * p.2, Real.sin φ * p.1 + Real.cos φ * p.2)

/-- (U-ROT) "Rotate coordinates so that u is the downward vertical" (sm-3:4428-4429), applied to the
SMOOTH diagram only: rotating a regular loop keeps the record it carries (parameters, pairing, cyclic
order, signs) and rotates every unit tangent.  The polygon `X` is not moved (record-level carrying). -/
theorem urot_exists_rotated (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X) (φ : ℝ) :
    ∃ F' : SmoothRegularLoop, F'.γ = rotationMap φ ∘ F.γ ∧ Nonempty (RecordCarried F' X) ∧
      ∀ t, SM.normalize (deriv F'.γ t) = rotationMap φ (SM.normalize (deriv F.γ t)) := by
  sorry

/-- (U-CURLS) the `R` curls (sm-3:4433-4455): from the rounding record of an all-negative polygon
diagram with `R` positively-crossed `u`-tangencies, `R` applications of cf:lem-curl (each disc inside
its rounding disc, disjoint supports) give a regular loop `F'` carrying a diagram `X'` with no
`u`-tangency at all, `P X' = P D̄`, writhe `w(D̄) − R`, every crossing negative. -/
theorem ucurl_exists_curled (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (u : Plane) (R : ℕ)
    (hcount : TangencyCount (Round C D ε h) u R)
    (hneg : ∀ x, D.toDiagram.sign x = -1) :
    ∃ (F' : SmoothRegularLoop) (X' : Diagram), Nonempty (RecordCarried F' X') ∧
      (∀ t, SM.normalize (deriv F'.γ t) ≠ u) ∧ P X' = P D.toDiagram ∧
      X'.writhe = D.toDiagram.writhe - R ∧ ∀ x, X'.sign x = -1 := by
  sorry

/-- (U-LIFT) the transverse lift (sm-3:4456-4523): a regular loop with no downward vertical tangency
carrying an all-negative diagram `X` lifts to a positive transverse knot whose front is the loop
(with the smaller-`y` over rule realising `X`'s over data) and carries `X`; the front's writhe is
`X`'s. -/
theorem ulift_exists_transverse_lift (F : SmoothRegularLoop) (X : Diagram) (c : RecordCarried F X)
    (hdown : ∀ t, SM.normalize (deriv F.γ t) ≠ ((0 : ℝ), (-1 : ℝ)))
    (hneg : ∀ x, X.sign x = -1) :
    ∃ K : TransverseKnot, xzOf K.T = F.γ ∧ Nonempty (K.front.Carries X) ∧
      K.front.writhe = X.writhe := by
  sorry

/-- (U-C) the assembly of clause (C) from the units, with the row-94 writhe bound as hypothesis
(sm-3:4525-4531 "By Theorem fd:contact, sl(K_T) = w(T) = −w − R … max deg_a P_{D̄} ≤ −sl(K_T) − 1"). -/
theorem cf_thm_carrierfloor_C_of_bound (hbound : TransverseFrontBound) : CarrierFloorCData := by
  sorry

/-- the row, once row 94 lands -/
theorem cf_thm_carrierfloor_of_bound (hbound : TransverseFrontBound) : CarrierFloorData where
  clauseR := cf_thm_carrierfloor_R
  clauseA := cf_thm_carrierfloor_A
  clauseB := cf_thm_carrierfloor_B
  clauseC := cf_thm_carrierfloor_C_of_bound hbound

/-! ## 8. Row 100 thm:floor (sm-3:4576-4585) -/

section Floor

open Carrier

variable {n : ℕ} [NeZero n]

/-- "either all turns are left, or exactly one turn is right" on the corner polygon `Q` (turns =
def:chirotope's `turn ∈ {−1, 0, +1}`, left = `1`) -/
def AllLeftOrOneRight {m : ℕ} (Q : LabelledTuple m) : Prop :=
  (∀ j, turn Q j = 1) ∨ (∃ j₀, turn Q j₀ = -1 ∧ ∀ j, j ≠ j₀ → turn Q j = 1)

/-- "after possibly reversing its orientation either all turns are left, or exactly one turn is
right": for the corner polygon of the subpolygon `Q` (accepted `ccpCornerPolygon`) or its reversal
(accepted `reversal`; `turn_reversal`) -/
def CarrierUniformOrOneDissent (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (S : Finset (Crossing P)) (q : Component hn hP S) : Prop :=
  AllLeftOrOneRight (ccpCornerPolygon hn hP S q) ∨
  AllLeftOrOneRight (reversal (ccpCornerPolygon hn hP S q))

/-- thm:floor: "Let Q be a subpolygon of a decomposition of a generic polygon, and suppose that
after possibly reversing its orientation either all turns are left, or exactly one turn is right.
Then mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q, H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0."
`H⁺_Q = cornerHomfly`, `m_Q = carrierCrossingCount`, `r_Q = carrierRotation`, `d_Q = cornerSlot`
(def:C, accepted; `cornerSlot_cast` is the printed equality `d_Q = 1 − m_Q − |r_Q|`). -/
structure FloorTheoremData : Prop where
  /-- "mindeg_a H⁺_Q ≥ 1 − m_Q − |r_Q| = d_Q" (in `ℤ` with `d_Q = cornerSlot`, and as printed with the
  real `r_Q`) -/
  a_floor : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    CarrierUniformOrOneDissent hn hP S q →
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧
    1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤
      (mindegAZ (cornerHomfly hn hP S q hS) : ℝ)
  /-- "H⁺_Q ∈ ℤ[a^{±1}, z²], so mindeg_z H⁺_Q ≥ 0" (no hypothesis on the turns) -/
  z_parity : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S),
    (∀ d k : ℤ, coeffAt d k (cornerHomfly hn hP S q hS) ≠ 0 → ∃ j : ℕ, k = 2 * (j : ℤ)) ∧
    0 ≤ mindegZZ (cornerHomfly hn hP S q hS)

/-! ### 8.1 Proof route of thm:floor (unit U-F) -/

/-- the `a`-floor from clause (C) on `C := carrierPolyComp`, `X := positiveLift` (`positiveLift_Γ` is
`Shadow.single (carrierPolyComp …)` by `rfl`; positivity `positiveLift_isPositive`; turns nonzero
lem:carriers (ii); the alternative from the turn signs via `principalTurn_sign`; then
`positiveLift_writhe_eq_carrierCrossingCount`, `carrierRotationInt_cast`, `cornerSlot_cast`). -/
theorem uf_a_floor_of_C (hC : CarrierFloorCData) (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (halt : CarrierUniformOrOneDissent hn hP S q) :
    cornerSlot hn hP S q ≤ mindegAZ (cornerHomfly hn hP S q hS) ∧
    1 - (carrierCrossingCount hn hP S q : ℝ) - |carrierRotation hn hP S q| ≤
      (mindegAZ (cornerHomfly hn hP S q hS) : ℝ) := by
  sorry

/-- the `z`-parity clause from lp:core's knot support (`positiveLift_componentCount = 1`,
`P_eq_homfly`, `mindegZZ_spec`) — provable now -/
theorem uf_z_parity (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S) (q : Component hn hP S) :
    (∀ d k : ℤ, coeffAt d k (cornerHomfly hn hP S q hS) ≠ 0 → ∃ j : ℕ, k = 2 * (j : ℤ)) ∧
    0 ≤ mindegZZ (cornerHomfly hn hP S q hS) := by
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
