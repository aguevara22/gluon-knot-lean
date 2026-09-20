import RProof.X1Rows
import RProof.X1Rows2
import RProof.GenericTransport
import CV.Rounding
import CV.Curl
import CV.UniformRot
import CV.ChamberInvRow
import Bridge.SmR
import SM.ALawful
import SM.CS5
import SM.CS3
import SM.CSilent
import SM.CChamber
import SM.HypR

/-! # CV/R tail — design sketch A (fidelity-first), 2026-09-15

Companion of work/drafts/cvtail/DESIGN_A.md.  Check: `cd work/lean && lake env lean ../drafts/cvtail/Sketch_A.lean`.
Rows: 155 CV:thm:carrierfloor (R)(A)(B)(C)(D), 165 CV:singleton_D_i, 174–178 R:generic_selected …
R:cv_theorem, 183 Bridge:theorem, 184 SM:corner_laws_and_soft.  STATEMENTS have no `sorry`; the
interface hypotheses of the other lanes are explicit Props / bundles (D-F11/D-F14 pattern, never
mapped); the leaves of the proof route are `sorry` and are listed in DESIGN_A.md §5.  Nothing here is
to be ported before the rows' statement reviews.  The fixed row names (`RProof.generic_selected`,
`RProof.extreme_pair_zero`, `RProof.extreme_transport`, `RProof.extreme_selected`, `RProof.cv_R`,
`Bridge.sm_R`, `SM.corner_laws_and_soft`) are NOT declared here (they denote theorems); their exact
statements are the accepted bundles of RProof/X1Rows.lean (rows 174–178) and the Props/bundles below
(183, 184); the conditional assemblies carry the suffix `_of_rows` / `_of`. -/

/-! ## 1. Assumed SM interface — row 99 cf:thm-carrierfloor, the memo shapes
(work/drafts/gap2/Gap2Statements.lean §7, copied verbatim; TO BE UNIFIED WITH LANE FLOOR, whose
Sketch_A/B differ from the memo in (A) `junction_local`, (B)'s normalised-orientation form and (C)'s
`f_D` clause — see DESIGN_A.md §2.1). -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-- "after reversing the orientation if necessary, either every principal turn is positive, or exactly
one is negative and every other is positive" (reversal negates every principal turn). -/
def UniformOrOneDissent (C : PolyComp) : Prop :=
  (∀ i, 0 < principalTurn C.P i) ∨
  (∃ i, principalTurn C.P i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn C.P j) ∨
  (∀ i, principalTurn C.P i < 0) ∨
  (∃ i, 0 < principalTurn C.P i ∧ ∀ j, j ≠ i → principalTurn C.P j < 0)

/-- (A) the rounding record `Round(L, D, ε) = (L_ε, D_ε)`: the accepted named construction. -/
def Round (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    RoundingWitness C D ε :=
  CornerRounding.roundedWitness h

/-- SM row 99 clause (R) (memo §7). -/
structure CarrierFloorRData : Prop where
  P_reverse : ∀ X : Diagram, X.componentCount = 1 → P X.reverse = P X
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  rot_reverse_polygon : ∀ (C : PolyComp), Regular C.P →
    rotationNumber (reversal C.P) = - rotationNumber C.P
  rot_reverse_curve : ∀ γ : ClosedC1Curve, γ.reverse.rot = - γ.rot

/-- SM row 99 clause (A) (memo §7). -/
structure CarrierFloorAData : Prop where
  one_record : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h h' : CornerRounding.Admissible C D ε), Round C D ε h = Round C D ε h'
  diagram_eq : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    Nonempty (Carried (Round C D ε h).Lε D.toDiagram)
  junction_local : ∀ (C C' : PolyComp) (D : PolygonDiagram C) (D' : PolygonDiagram C') (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (h' : CornerRounding.Admissible C' D' ε)
    (j : ℕ) (j' : ℕ), j < C.k → j' < C'.k →
    C.P j = C'.P j' → CornerRounding.uDir C j = CornerRounding.uDir C' j' →
    CornerRounding.vDir C j = CornerRounding.vDir C' j' →
    (Round C D ε h).Lε.γ '' Set.Icc ((Round C D ε h).a j) ((Round C D ε h).b j) =
      (Round C' D' ε h').Lε.γ '' Set.Icc ((Round C' D' ε h').a j') ((Round C' D' ε h').b j')
  rest_is_L : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε)
    (p : Plane), p ∉ (⋃ i, cornerDisc C ε i) → (p ∈ Set.range (Round C D ε h).Lε.γ ↔ p ∈ polygonImage C)

/-- SM row 99 clause (B) (memo §7). -/
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

/-- the hypotheses of SM row 99 clause (C) (memo §7). -/
structure CarrierFloorCHyp (C : PolyComp) (X : Diagram) : Prop where
  shadow : X.Γ = Shadow.single C
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  turn_ne : ∀ i, principalTurn C.P i ≠ 0
  turn_lt_pi : ∀ i, |principalTurn C.P i| < Real.pi
  alternative : UniformOrOneDissent C

/-- SM row 99 clause (C) (memo §7). -/
structure CarrierFloorCData : Prop where
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  floor_support : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ∀ d k : ℤ, coeffAt d k (P X) ≠ 0 → ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (d : ℝ)

end

end SM

/-! ## 2. Row 155 CV:thm:carrierfloor (d3_floor.tex:736–807) — the CV statements

(R)(A)(B)(C) are the SM row-99 clauses word for word (plan F6; the two texts differ only in the scoping
sentence "Here rot is as in Definition def:rot", in (R)'s knot-level phrasing "Let K be an oriented knot",
in (B)'s domain "a diagrammatic closed polygon (Definition def:diagrammatic)" and in (C)'s "no generic
parent polygon is assumed" commentary).  They are stated on CV's printed domain through the accepted
polygon bridge of CV/Rounding.lean §1 (`polyComp L hreg`, `OverUnder.toPolygonDiagram`, `clearance`,
`roundingRecord`), exactly as the accepted CV:lem:rounding was, and PROVED from the SM bundles by the
conditional theorems `carrierfloor_*_of_sm` (D-F11 pattern).  (D) is CV-only and PROVED here. -/

namespace CV

open SM SM.Link SM.GeoCarrier
open scoped ContDiff

noncomputable section
open Classical

/-- "after reversing the orientation if necessary, either every principal turn is positive, or exactly
one is negative [and every other is positive]" on a labelled polygon, in CV's vocabulary
(`CV.principalTurn`); definitionally `SM.UniformOrOneDissent (polyComp L hreg)`. -/
def TurnsUniformOrOneDissent {c : ℕ} (L : LabelledTuple c) : Prop :=
  (∀ i, 0 < principalTurn L i) ∨
  (∃ i, principalTurn L i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn L j) ∨
  (∀ i, principalTurn L i < 0) ∨
  (∃ i, 0 < principalTurn L i ∧ ∀ j, j ≠ i → principalTurn L j < 0)

theorem turnsUniformOrOneDissent_iff_sm {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) :
    TurnsUniformOrOneDissent L ↔ SM.UniformOrOneDissent (polyComp L hreg) := Iff.rfl

/-- **(R)** "Let K be an oriented knot and −K the same knot with its orientation reversed. Then
P_{−K} = P_K. Moreover a diagram of −K obtained by reversing the orientation of a diagram of K has the
same crossing signs, the same writhe, and rotation number of the underlying plane curve negated"
(d3:739–743), with `P_K = homfly` (CV:def:homfly) and "rot as in Definition def:rot" (`CV.rot` for a
polygon, `CV.rotCurve` for a C¹ curve). -/
structure CarrierFloorRData : Prop where
  /-- "P_{−K} = P_K", read on a diagram `X` of `K` -/
  homfly_reverse : ∀ X : Diagram, X.componentCount = 1 → homfly X.reverse = homfly X
  /-- "P_{−K} = P_K": for any two diagrams `X`, `X'` of the knot `K` -/
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → homfly X'.reverse = homfly X
  /-- "the same crossing signs" -/
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  /-- "the same writhe" -/
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  /-- "rotation number of the underlying plane curve negated" — polygonal curve, CV:def:rot -/
  rot_reverse_polygon : ∀ {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L)
    (hL' : Regular (reversal L)), rot (reversal L) hL' = -rot L hL
  /-- — C¹ regular curve, CV:def:rot's `rot(γ) = tw(T_γ)` -/
  rot_reverse_curve : ∀ γ : ClosedC1Curve, rotCurve γ.reverse = -rotCurve γ

/-- **(A)** "For every ε ∈ (0, ε₀(L)), the construction in the proof of that lemma returns one curve and
one diagram at those data: the junction inserted at the corner q_i is determined by ε, by the two
incident unit directions and by the transition profile …; the arc length ℓ is then determined by the
endpoint condition, and the rest of the curve is L itself. Write Round(L,D,ε) = (L_ε, D_ε)"
(d3:745–760).  `Round(L, D, ε)` is the accepted `CV.roundingRecord` (= SM's `roundedWitness`). -/
structure CarrierFloorAData : Prop where
  /-- "one curve and one diagram at those data" -/
  one_record : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (h1 h2 : 0 < ε) (h3 h4 : ε < clearance L hreg),
    roundingRecord hL hreg hturn D h1 h3 = roundingRecord hL hreg hturn D h2 h4
  /-- "D_ε", the rounded diagram, is `D` carried by `L_ε` -/
  diagram_carried : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    Nonempty (Carried (roundingRecord hL hreg hturn D hε hε₀).Lε (D.toPolygonDiagram hL).toDiagram)
  /-- "the junction inserted at the corner q_i is determined by ε, by the two incident unit
  directions and by the transition profile, which is fixed once and for all" -/
  junction_local : ∀ {n n' : ℕ} [NeZero n] [NeZero n'] (L : LabelledTuple n) (L' : LabelledTuple n')
    (hL : Diagrammatic L) (hL' : Diagrammatic L') (hreg : Regular L) (hreg' : Regular L')
    (hturn : ∀ i, principalTurn L i ≠ 0) (hturn' : ∀ i, principalTurn L' i ≠ 0)
    (D : OverUnder (polyComp L hreg)) (D' : OverUnder (polyComp L' hreg')) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) (hε₀' : ε < clearance L' hreg') (j j' : ℕ),
    j < n → j' < n' → L j = L' j' →
    CornerRounding.uDir (polyComp L hreg) j = CornerRounding.uDir (polyComp L' hreg') j' →
    CornerRounding.vDir (polyComp L hreg) j = CornerRounding.vDir (polyComp L' hreg') j' →
    (roundingRecord hL hreg hturn D hε hε₀).Lε.γ ''
        Set.Icc ((roundingRecord hL hreg hturn D hε hε₀).a j) ((roundingRecord hL hreg hturn D hε hε₀).b j) =
      (roundingRecord hL' hreg' hturn' D' hε hε₀').Lε.γ ''
        Set.Icc ((roundingRecord hL' hreg' hturn' D' hε hε₀').a j')
          ((roundingRecord hL' hreg' hturn' D' hε hε₀').b j')
  /-- "the rest of the curve is L itself" -/
  rest_is_L : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) (p : Plane),
    p ∉ (⋃ i, cornerDisc (polyComp L hreg) ε i) →
    (p ∈ Set.range (roundingRecord hL hreg hturn D hε hε₀).Lε.γ ↔ p ∈ ⋃ i : ZMod n, edgeSegment L i)

/-- **(B)** "Let L be a diagrammatic closed polygon whose principal turns all exist and are nonzero,
carrying a diagram D, and assume, after reversing the orientation of L if necessary, that either every
principal turn is positive, or exactly one is negative. Put R = |rot(L)|. Then there are a direction
u ∈ S¹ and an ε₁ > 0 such that for every ε ∈ (0, ε₁) the rounded curve L_ε of the record Round(L,D,ε)
from clause (A) has exactly R points at which its unit tangent equals u and exactly R at which it equals
−u; at each of them the tangent crosses that direction in the positive sense" (d3:761–776).
`R = rotAbs L hreg` (CV:def:rot); ε₁ ≤ ε₀(L) so that the record exists (the printed proof takes
ε₁ = ε₀(L)). -/
structure CarrierFloorBData : Prop where
  tangencies : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)),
    TurnsUniformOrOneDissent L →
    ∃ (u : Plane) (ε₁ : ℝ), euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ clearance L hreg ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (hε₀ : ε < clearance L hreg), ε < ε₁ →
        ({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ (roundingRecord hL hreg hturn D hε hε₀).T t = u}.ncard =
            rotAbs L hreg) ∧
        ({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ (roundingRecord hL hreg hturn D hε hε₀).T t = -u}.ncard =
            rotAbs L hreg) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) 1,
          ((roundingRecord hL hreg hturn D hε hε₀).T t = u ∨
            (roundingRecord hL hreg hturn D hε hε₀).T t = -u) →
          ∃ j, j < n ∧ t ∈ Set.Ioo ((roundingRecord hL hreg hturn D hε hε₀).a j)
              ((roundingRecord hL hreg hturn D hε hε₀).b j) ∧
            0 < deriv ((roundingRecord hL hreg hturn D hε hε₀).θ j) t)

/-- The hypotheses of **(C)** (d3:777–795) on the oriented knot diagram `X` "whose underlying plane
curve is a closed polygon L": "all of whose crossings are positive" (`positive`); "with all principal
turns existing" (`hreg : Regular L`, a parameter), "nonzero" (`turn_ne`), "and of magnitude below π"
(`turn_lt_pi`); "with finitely many double points, all transversal, with no triple points, none of them
a corner of L, and no corner of L lying on a non-incident edge" (`hL : Diagrammatic L`, the parameter
of the row — "The no-triple condition repeats the shared-image clause of Definition def:diagrammatic");
"after reversing the orientation if necessary … either every principal turn is positive, or exactly
one is negative and every other is positive" (`alternative`). -/
structure CarrierFloorCHyp {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) (X : Diagram) :
    Prop where
  shadow : X.Γ = Shadow.single (polyComp L hreg)
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  turn_ne : ∀ i, principalTurn L i ≠ 0
  turn_lt_pi : ∀ i, |principalTurn L i| < Real.pi
  alternative : TurnsUniformOrOneDissent L

/-- **(C)** "Then min deg_a P_D(a,z) ≥ 1 − w − R (eq:floor), and the same bound holds for
f_D(a) = [z^0]P_D(a,z) whenever f_D ≠ 0" (d3:796–801); `w = X.writhe`, `R = rotAbs L hreg`,
`P_D = homfly X`; the `f_D` clause in support form (every monomial `a^d z^0` present in `P_D` has
`d ≥ 1 − w − R`; vacuous when `f_D = 0`). -/
structure CarrierFloorCData : Prop where
  floor : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (_hL : Diagrammatic L) (hreg : Regular L)
    (X : Diagram), CarrierFloorCHyp L hreg X →
    1 - X.writhe - (rotAbs L hreg : ℤ) ≤ mindegAZ (homfly X)
  floor_z0 : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (_hL : Diagrammatic L) (hreg : Regular L)
    (X : Diagram), CarrierFloorCHyp L hreg X →
    ∀ d : ℤ, coeffAt d 0 (homfly X) ≠ 0 → 1 - X.writhe - (rotAbs L hreg : ℤ) ≤ d

/-- **(D)** "Let P be generic, let S ∈ Ind(G_P) and let L be a carrier of S carrying no residual piece,
so that P_{S,L} = 1 and w_{S,L} = 0 by Definition def:X1's empty conventions …, and suppose that all its
principal turns are nonzero and that, after reversing the orientation if necessary, either every turn is
positive or exactly one is negative. Then R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥ 1 − w_{S,L} − R(L)"
(d3:802–807), on CV:def:X1's accepted objects; the turns are those of the carrier's corner polygon
(CV:def:wind, CV:def:rot). -/
structure CarrierFloorDData : Prop where
  floor_D : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hG : Generic P)
    (S : Finset (Crossing P)) (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    piecesOn hG.crossingGeometry S q = ∅ →
    (∀ j, principalTurn (geoCornerPolygon hG.crossingGeometry S q) j ≠ 0) →
    TurnsUniformOrOneDissent (geoCornerPolygon hG.crossingGeometry S q) →
    (groupedPoly hn hG hS q = 1 ∧ groupedWrithe hG q = 0) ∧
    1 ≤ carrierR hn hG hS q ∧
    mindegAZ (groupedPoly hn hG hS q) = 0 ∧ 1 - groupedWrithe hG q - (carrierR hn hG hS q : ℤ) ≤ 0

/-- Row 155: the five clauses (proposed row declaration `CV.carrierfloor : CarrierFloorData`). -/
structure CarrierFloorData : Prop where
  clauseR : CarrierFloorRData
  clauseA : CarrierFloorAData
  clauseB : CarrierFloorBData
  clauseC : CarrierFloorCData
  clauseD : CarrierFloorDData

/-! ### 2.1 The bridges (R)(A)(B)(C): CV = SM read on the polygon bridge (D-F11 conditional theorems) -/

/-- (R) from SM's (R): `P = homfly` (lp:core), the polygon clause is the accepted `CV.rot_reversal`. -/
theorem carrierfloor_R_of_sm (h : SM.CarrierFloorRData) : CarrierFloorRData where
  homfly_reverse := fun X hX => by
    rw [← lp_core.eq_homfly, ← lp_core.eq_homfly]; exact h.P_reverse X hX
  knot_reverse := fun X X' hX hXX' => by
    rw [← lp_core.eq_homfly, ← lp_core.eq_homfly]; exact h.knot_reverse X X' hX hXX'
  sign_reverse := h.sign_reverse
  writhe_reverse := h.writhe_reverse
  rot_reverse_polygon := by
    intro c _ L hL hL'
    exact rot_reversal hL hL'
  rot_reverse_curve := h.rot_reverse_curve

/-- (A) from SM's (A) at `polyComp L hreg`, `D.toPolygonDiagram hL` (`Round … = roundingRecord …` is
`rfl`); `rest_is_L` is already the accepted `CV.rounding.a` on the record. -/
theorem carrierfloor_A_of_sm (h : SM.CarrierFloorAData) : CarrierFloorAData where
  one_record := fun _ _ _ _ _ _ _ _ _ _ => rfl
  diagram_carried := fun _ hL _ hturn D _ hε hε₀ => ⟨(roundingRecord hL _ hturn D hε hε₀).carried⟩
  junction_local := by
    intro n n' _ _ L L' hL hL' hreg hreg' hturn hturn' D D' ε hε hε₀ hε₀' j j' hj hj' hLL hu hv
    exact h.junction_local (polyComp L hreg) (polyComp L' hreg') (D.toPolygonDiagram hL)
      (D'.toPolygonDiagram hL') ε (roundingAdmissible hL hreg hturn D hε hε₀)
      (roundingAdmissible hL' hreg' hturn' D' hε hε₀') j j' hj hj' hLL hu hv
  rest_is_L := fun L hL hreg hturn D ε hε hε₀ p hp =>
    (rounding.a L hL hreg D ε (roundingRecord hL hreg hturn D hε hε₀)).1 p hp

/-- `|rot(L)|` in CV's integer form is `|rotationNumber L|` (accepted `rotAbs_cast`,
`rot_eq_rotationNumber`). -/
theorem rotAbs_intCast_real {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) :
    ((rotAbs L hreg : ℤ) : ℝ) = |rotationNumber L| := by
  rw [rotAbs_cast, Int.cast_abs, rot_eq_rotationNumber hreg]

/-- (B) from SM's (B) at the bridge; the tangency counts read `R = rotAbs L hreg`. -/
theorem carrierfloor_B_of_sm (h : SM.CarrierFloorBData) : CarrierFloorBData where
  tangencies := by
    intro n _ L hL hreg hturn D halt
    obtain ⟨u, ε₁, hu, hε₁, hclear, hall⟩ :=
      h.tangencies (polyComp L hreg) (D.toPolygonDiagram hL) hturn halt
    refine ⟨u, ε₁, hu, hε₁, hclear, fun ε hε hε₀ hlt => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hall ε (roundingAdmissible hL hreg hturn D hε hε₀) hlt
    have hR := rotAbs_intCast_real L hreg
    refine ⟨?_, ?_, h3⟩
    · have h1' : ({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ (roundingRecord hL hreg hturn D hε hε₀).T t = u}.ncard : ℝ)
          = ((rotAbs L hreg : ℤ) : ℝ) := by rw [hR]; exact h1
      exact_mod_cast h1'
    · have h2' : ({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ (roundingRecord hL hreg hturn D hε hε₀).T t = -u}.ncard : ℝ)
          = ((rotAbs L hreg : ℤ) : ℝ) := by rw [hR]; exact h2
      exact_mod_cast h2'

/-- (C) from SM's (C) at the bridge (`P = homfly`, `R = rotAbs`). -/
theorem carrierfloor_C_of_sm (h : SM.CarrierFloorCData) : CarrierFloorCData where
  floor := by
    intro n _ L _hL hreg X hX
    have hyp : SM.CarrierFloorCHyp (polyComp L hreg) X :=
      ⟨hX.shadow, hX.positive, hX.turn_ne, hX.turn_lt_pi, hX.alternative⟩
    have := h.floor _ X hyp
    have hR : |rotationNumber (polyComp L hreg).P| = ((rotAbs L hreg : ℤ) : ℝ) :=
      (rotAbs_intCast_real L hreg).symm
    rw [lp_core.eq_homfly, hR] at this
    exact_mod_cast this
  floor_z0 := by
    intro n _ L _hL hreg X hX d hd
    have hyp : SM.CarrierFloorCHyp (polyComp L hreg) X :=
      ⟨hX.shadow, hX.positive, hX.turn_ne, hX.turn_lt_pi, hX.alternative⟩
    have := h.floor_support _ X hyp d 0 (by rwa [lp_core.eq_homfly])
    have hR : |rotationNumber (polyComp L hreg).P| = ((rotAbs L hreg : ℤ) : ℝ) :=
      (rotAbs_intCast_real L hreg).symm
    rw [hR] at this
    exact_mod_cast this

/-! ### 2.2 Clause (D) — PROVED NOW from CV:lem:uniformrot and CV:def:X1's empty conventions -/

/-- `mindeg_a 1 = 0`. -/
theorem mindegAZ_one : mindegAZ (1 : R) = 0 := by
  have h : mindegA (1 : R) = ((0 : ℤ) : WithTop ℤ) := by
    rw [AddMonoidAlgebra.one_def]
    exact mindegA_single 0 0 one_ne_zero
  rw [mindegAZ, h, WithTop.untopD_coe]

/-- `|rot(L)| ≥ 1` for a regular polygon with nonzero turns, uniform or one-dissent after reversal:
CV:lem:uniformrot (i) in the two uniform cases, (ii) in the one-dissent case, and (ii) on the reversal
(`rot_reversal`, `principalTurn_reversal`) when the dissenting turn is the positive one. -/
theorem one_le_abs_rot_of_alternative {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : Regular L)
    (h : TurnsUniformOrOneDissent L) : 1 ≤ |rot L hL| := by
  rcases h with hpos | ⟨a, ha, hother⟩ | hneg | ⟨a, ha, hother⟩
  · exact le_trans (uniformrot.pos_ge_one c L hL hpos) (le_abs_self _)
  · exact le_trans (uniformrot.one_dissent c L hL a ha (fun i hi => (hother i hi).le)).2 (le_abs_self _)
  · have h1 := uniformrot.neg_le_neg_one c L hL hneg
    calc (1 : ℤ) ≤ -rot L hL := by linarith
      _ ≤ |rot L hL| := neg_le_abs _
  · have hL' : Regular (reversal L) := regular_reversal' hL
    have hrev := rot_reversal hL hL'
    have hpt : ∀ i, principalTurn (reversal L) i = -principalTurn L (2 - i) := fun i =>
      SM.principalTurn_reversal ((regular_iff_sm L).mp hL) i
    have ha' : principalTurn (reversal L) (2 - a) < 0 := by
      rw [hpt, sub_sub_cancel]; linarith
    have hother' : ∀ i, i ≠ 2 - a → 0 ≤ principalTurn (reversal L) i := by
      intro i hi
      rw [hpt]
      have hne : 2 - i ≠ a := fun h => hi (by rw [← h]; ring)
      linarith [hother (2 - i) hne]
    have h1 := (uniformrot.one_dissent c (reversal L) hL' (2 - a) ha' hother').2
    rw [hrev] at h1
    calc (1 : ℤ) ≤ -rot L hL := h1
      _ ≤ |rot L hL| := neg_le_abs _

/-- **Row 155 (D)**, PROVED: `P_{S,L} = 1`, `w_{S,L} = 0` (CV:def:X1 empty conventions), `R(L) ≥ 1`
(CV:lem:uniformrot on the carrier's corner polygon), `mindeg_a 1 = 0`, `1 − 0 − R(L) ≤ 0`. -/
theorem carrierfloor_D : CarrierFloorDData where
  floor_D := by
    intro n _ hn P hG S hS q hempty _hturn halt
    have hpoly : groupedPoly hn hG hS q = 1 := groupedPoly_of_piecesOn_eq_empty hn hG hS q hempty
    have hwr : groupedWrithe hG q = 0 := groupedWrithe_of_piecesOn_eq_empty hG q hempty
    have hR : 1 ≤ (carrierR hn hG hS q : ℤ) := by
      rw [carrierR_cast]
      exact one_le_abs_rot_of_alternative (carrierPolygon_cvRegular hn hG hS q) halt
    refine ⟨⟨hpoly, hwr⟩, by exact_mod_cast hR, ?_, ?_⟩
    · rw [hpoly]; exact mindegAZ_one
    · rw [hwr]; omega

/-- Row 155 assembled from the SM row-99 clauses (conditional, D-F11): the row theorem
`CV.carrierfloor` is this applied to the floor lane's `SM.cf_thm_carrierfloor` clauses. -/
theorem carrierfloor_of_sm (hR : SM.CarrierFloorRData) (hA : SM.CarrierFloorAData)
    (hB : SM.CarrierFloorBData) (hC : SM.CarrierFloorCData) : CarrierFloorData where
  clauseR := carrierfloor_R_of_sm hR
  clauseA := carrierfloor_A_of_sm hA
  clauseB := carrierfloor_B_of_sm hB
  clauseC := carrierfloor_C_of_sm hC
  clauseD := carrierfloor_D

/-! ## 3. Row 165 CV:singleton_D_i — thm:s7universal (D)(i) (d6_vertexedge.tex:2682–2687)

"(i) Let S ∈ Ind(G_P), let A be a uniform carrier of S, and let {c} be a singleton residual piece of S
carried by A. Then min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2, so the factor Ω₁(S,A) of Definition def:X1
is zero."  `f_A = [z^0] P_{S,A}` (def:markeddata, d6:1157–1166), `P_{S,A} = groupedPoly`,
`1 − w_{S,A} − R(A) = slot` (CV:def:X1), `Ω₁(S,A) = Omega1`; "uniform carrier" = CV:def:wind's
`CarrierUniform`; "{c} a singleton residual piece of S carried by A" = `c ∈ U(S)`, the piece of `c` has
label set `{c}`, and that piece is assigned to `A` (def:X1's `piecesOn`). The degree bound in support
form (every `a^d z^0` present in `P_{S,A}` has `d ≥ slot + 2`; "min deg_a f_A ≥ …" with `f_A ≠ 0`
understood, as the R consumer reads it). -/

structure SingletonDiData : Prop where
  degree_gap : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hG : Generic P)
    (S : Finset (Crossing P)) (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ (c : Crossing P) (hc : c ∈ U hG.crossingGeometry S),
      pieceLabels hG.crossingGeometry S (pieceOf hG.crossingGeometry S c hc) = {c} →
      pieceOf hG.crossingGeometry S c hc ∈ piecesOn hG.crossingGeometry S q →
      ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d
  factor_zero : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hG : Generic P)
    (S : Finset (Crossing P)) (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ (c : Crossing P) (hc : c ∈ U hG.crossingGeometry S),
      pieceLabels hG.crossingGeometry S (pieceOf hG.crossingGeometry S c hc) = {c} →
      pieceOf hG.crossingGeometry S c hc ∈ piecesOn hG.crossingGeometry S q →
      Omega1 hn hG hS q = 0

/-- "so the factor Ω₁(S,A) … is zero": the coefficient at the slot lies two degrees below the lowest
present degree. PROVED (the printed "so"). -/
theorem omega1_eq_zero_of_gap {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hgap : ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) :
    Omega1 hn hG hS q = 0 := by
  by_contra hne
  have := hgap (slot hn hG hS q) hne
  omega

/-- The bundle from its first field. PROVED. -/
theorem SingletonDiData.of_degree_gap
    (hgap : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hG : Generic P)
      (S : Finset (Crossing P)) (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
      CarrierUniform hG.crossingGeometry S q →
      ∀ (c : Crossing P) (hc : c ∈ U hG.crossingGeometry S),
        pieceLabels hG.crossingGeometry S (pieceOf hG.crossingGeometry S c hc) = {c} →
        pieceOf hG.crossingGeometry S c hc ∈ piecesOn hG.crossingGeometry S q →
        ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) :
    SingletonDiData where
  degree_gap := hgap
  factor_zero := fun hn P hG S hS q hq c hc hpiece hown =>
    omega1_eq_zero_of_gap hn hG hS q (hgap hn P hG S hS q hq c hc hpiece hown)

/-- **Row 165 modulo row 155 (C)** (the route of d6:2890–2947: `S' = S ∪ {c}` independent, the pieces of
`S'` are those of `S` minus `{c}`, smoothing `c` splits `A` into `Λ₁, Λ₂` carrying them (CV:lem:carriers
(iv) at `S'`), `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}`, `w_{S,A} = w₁ + w₂ + 1`, knot parity ⇒ `f_A = f₁ f₂`,
`rot(A) = rot(Λ₁) + rot(Λ₂)` with one loop uniform and one one-dissent (turnlift (ii)), uniformrot ⇒
`R(A) = R(Λ₁) + R(Λ₂)`, clause (C) on each loop through cor:groupedknot (B) / clause (D)). LEAF. -/
theorem singleton_D_i_of_floor (_hC : CarrierFloorCData) : SingletonDiData := by
  sorry

end

end CV

/-! ## 4. Rows 174–178 — the frozen statements (RProof/X1Rows.lean, accepted) and the assembly

The statements of rows 174–177 are the accepted bundles `GenericSelectedData`, `ExtremePairZeroData`,
`ExtremeTransportData`, `ExtremeSelectedData` in the fixed row shape (`RowShape` below, the shape of
the accepted siblings `exterior`, `availability_zero_one`, `generic_selector`, `generic_transport`); row
178 is `RProof.cv_R : CV.hyp_R`.  The assembly of 178 from 174–177 is PROVED here (`cv_R_of_rows`), so
`RProof.cv_R := cv_R_of_rows generic_selected extreme_pair_zero extreme_transport extreme_selected`
once the four rows are theorems. -/

namespace RProof

open SM

/-- The fixed shape of an X₁-dependent R row (the accepted siblings' signature with `hn` explicit). -/
def RowShape (D : ∀ {n : ℕ} [NeZero n], 3 ≤ n → CV.Event n → ZMod n → ZMod n → ZMod n → ℝ → Prop) :
    Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g → ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ D hn E e f g δ

/-- The accepted rows 170, 172, 173 in the shape. -/
theorem rowShape_170 : RowShape @AvailabilityZeroOneData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => availability_zero_one hn E e f g h3 h4e h4f h4g hE
theorem rowShape_172 : RowShape @GenericSelectorData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_selector hn E e f g h3 h4e h4f h4g hE
theorem rowShape_173 : RowShape @GenericTransportData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_transport hn E e f g h3 h4e h4f h4g hE

/-- CV:prop:chamberinv (ii) (row 147, accepted `CV.chamberinv_ii`) in the R lane's `ChamberInvII` form. -/
theorem chamberInvII_of_row147 : ChamberInvII :=
  fun _ _ hn _ _ hP hQ h => (CV.chamberinv_ii hn hP hQ h).symm

/-- **Row 178 modulo rows 174–177**, PROVED: R_ASSEMBLY_SPEC.md (3)–(4) summed (`A2_cvRNear_of_rows`,
accepted) and R6 `cv_R = cv_R_near + chamberinv(ii)` (`hyp_R_of_near_of_chamberinv`, accepted).
`RProof.cv_R : CV.hyp_R := cv_R_of_rows generic_selected extreme_pair_zero extreme_transport
extreme_selected`. -/
theorem cv_R_of_rows (h174 : RowShape @GenericSelectedData) (h175 : RowShape @ExtremePairZeroData)
    (h176 : RowShape @ExtremeTransportData) (h177 : RowShape @ExtremeSelectedData) : CV.hyp_R :=
  hyp_R_of_near_of_chamberinv
    (A2_cvRNear_of_rows rowShape_170 rowShape_172 rowShape_173 h174 h175 h176 h177)
    chamberInvII_of_row147

/-- Row 175 modulo row 165: the three presupposition fields are the accepted `PRE_175_*`; the row's
`pair_row_zero` is CV:singleton_D_i on the carrier owning `{z}` (R_EXTREME_PAIR_ZERO_PROOF.md, proof
paragraphs 4–5: "If wind(S) = 0, the X1 term is zero by definition. Otherwise every carrier of S is
uniform. Let A be the carrier owning {z} … Ω₁(S,A) = 0"). LEAF (unit PZ, ~150 lines). -/
theorem extreme_pair_zero_of_singleton (_h165 : CV.SingletonDiData) : RowShape @ExtremePairZeroData := by
  sorry

end RProof

/-! ## 5. Row 183 Bridge:theorem — `Bridge.sm_R : SM.hyp_R` (BRIDGE.md §3 (19)–(21)) -/

namespace Bridge

/-- **Row 183 modulo row 178**, PROVED (the accepted `SM.sm_R_of_cv_R`, the library theorem of
Bridge/SmR.lean): `Bridge.sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R`. The row is a restatement of
that library theorem at the proved `RProof.cv_R`, not a new proof: B1–B3 make the SM triple germ a simple
transversal RIII event, `CV.hyp_R` gives `X₁(P₊) = X₁(P₋)` (20), B4 (17)/(18) replaces both sides by `C`
(21). -/
theorem sm_R_of_cv_R (hcv : CV.hyp_R) : SM.hyp_R := SM.sm_R_of_cv_R hcv

/-- The same, from the four open R rows. -/
theorem sm_R_of_rows (h174 : RProof.RowShape @RProof.GenericSelectedData)
    (h175 : RProof.RowShape @RProof.ExtremePairZeroData)
    (h176 : RProof.RowShape @RProof.ExtremeTransportData)
    (h177 : RProof.RowShape @RProof.ExtremeSelectedData) : SM.hyp_R :=
  SM.sm_R_of_cv_R (RProof.cv_R_of_rows h174 h175 h176 h177)

end Bridge

/-! ## 6. Row 184 SM:corner_laws_and_soft — the final theorem (TARGETS.md "Exact final target")

"Prove that the corner state sum C of SM def:C satisfies every wall law on the domains of SM
cor:A-lawful, together with SM thm:C-soft in every soft sector. … Define its conclusion as the
conjunction of these actual C identities, with their printed quantifiers, signs and domains. … Required
coverage: chamber constancy and silent-wall invariance; the flat deletion law; both bigon branches and
the sliding branch of the vertex-edge law, with the stated sign and the actual two child polygons;
triple-wall invariance at every source simple triple wall, after proving R; the full cusp jump on the
source domain (the deletion satisfies G1), including threaded cusps; retain the direct empty-cusp zero
result; the soft theorem in every sector, including zero-selector sectors. Use the normalizations and
reversal/cyclic identities inherited with cor:A-lawful as stated there."

The accepted identities enter as their accepted bundles (`CChamberData`, `CSilentData`, `CS3Data`,
`CS5Data`, `hyp_R`); the pending ones as Props in the shape of cor:A-lawful's accepted `ALawfulData`
fields with `amplitude` replaced by `cornerStateSum` (TO BE UNIFIED WITH LANE CORNER: thm:C-S7,
thm:C-soft, cor:C-inherits). -/

namespace SM

open WallGerm SoftDuplication

/-- thm:C-S7 (sm-4:267–275): "At a simple vertex–edge wall at (M;a), of bigon or sliding type, with
halves λ₁, λ₂ and contact sign s = χ_{a,a+1,M}(P₋), C(P₊) − C(P₋) = s C(λ₁) C(λ₂)"; the halves are
generic (lem:children (ii), the domain check of cor:C-inherits), both branches covered by
`VertexEdgeAt` (`vertexEdge_bigon_or_sliding`). -/
def VertexEdgeLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (hc : g.VertexEdgeAt M a),
    ∃ (h1 : Generic (firstHalf g.center M a)) (h2 : Generic (secondHalf g.center M a)),
      ∀ tp tm : g.SideParameter,
        cornerStateSum hn (g.sideTuple true tp).2 - cornerStateSum hn (g.sideTuple false tm).2 =
          (g.contactSign M a : ℤ) *
            (cornerStateSum (contactHalfSizes_bounds hn hc.1).1.1 h1 *
              cornerStateSum (contactHalfSizes_bounds hn hc.1).2.1 h2)

/-- cor:C-inherits' cusp law (sm-6:313–319): "C(P_loop) − C(P_no) = −κ C(P(0) ∖ j)" on cor:A-lawful's
domain ("when the deletion satisfies (G1)"), the deletion shown generic (the domain check of the printed
proof, sm-6:335–345), including threaded cusps (no emptiness hypothesis). -/
def CuspLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j)
    (_hQ : G1 (deleteVertex w.center j)),
    ∃ b : Bool, CuspCase w.center j b ∧ (∀ b' : Bool, CuspCase w.center j b' → b' = b) ∧
      ∃ κ : ℤ, (κ = -1 ∨ κ = 1) ∧ ∃ hQ' : Generic (deleteVertex w.center j),
        ∀ s t : w.SideParameter,
          (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
            rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val = (κ : ℝ)) ∧
          cornerStateSum (by have := hf.1; omega) (w.sideTuple (w.cuspLoopSide b j) s).2 -
              cornerStateSum (by have := hf.1; omega) (w.sideTuple (!(w.cuspLoopSide b j)) t).2 =
            -κ * cornerStateSum (by have := hf.1; omega) hQ'

/-- thm:C-soft (sm-4:984–992): "for all sufficiently small ε > 0, C(P_ε) = ((χ₋ + χ₊)/2) C(P)", every
admissible `q` (every sector, zero-selector sectors included), `P_ε` generic for small `ε`
(lem:soft-generic). -/
def SoftTheoremC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (j : ZMod n) (q : Plane),
    SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega) hQ : ℚ) = softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

/-- cor:A-lawful's reversal identity inherited by `C` (cor:C-inherits): `C(P̄) = (−1)^n C(P)`. -/
def ReversalLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn ((generic_reversal P).mpr hP) = (-1) ^ n * cornerStateSum hn hP

/-- cor:A-lawful's cyclic identity: `C` is a function of the polygon (def:C's cyclic quotient). -/
def CyclicLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : GenericTuple n) (a : ZMod n),
    cornerStateSum hn (genericShift a P).2 = cornerStateSum hn P.2

/-- cor:A-lawful's normalizations inherited by `C`: `C(K₁) = −1`, `C(K₋₁) = +1`. -/
def TrianglesC : Prop :=
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.1 = -1 ∧
  cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.2.1 = 1

/-- **Row 184, the statement**: the conjunction of the actual `C` identities, each on its printed domain
(proposed row declaration `SM.corner_laws_and_soft : CornerLawsAndSoftData`). -/
structure CornerLawsAndSoftData : Prop where
  /-- prop:C-chamber -/
  chamber : CChamberData
  /-- prop:C-silent (E) and (C) -/
  silent : CSilentData
  /-- thm:C-S3 -/
  flat : CS3Data
  /-- thm:C-S7, both bigon branches and sliding -/
  vertex_edge : VertexEdgeLawC
  /-- hyp:R, proved (Bridge:theorem): triple-wall invariance -/
  triple : hyp_R
  /-- cor:C-inherits: the full cusp jump on the source domain -/
  cusp : CuspLawC
  /-- thm:C-S5, retained -/
  empty_cusp : CS5Data
  /-- thm:C-soft in every sector -/
  soft : SoftTheoremC
  /-- cor:C-inherits: reversal -/
  reversal : ReversalLawC
  /-- cyclic descent (def:C) -/
  cyclic : CyclicLawC
  /-- cor:C-inherits: the triangle values -/
  triangles : TrianglesC

/-- **Row 184 modulo hyp:R and the corner lane**, PROVED from the accepted rows prop:C-chamber,
prop:C-silent, thm:C-S3, thm:C-S5 and def:C's cyclic invariance: `SM.corner_laws_and_soft :=
corner_laws_and_soft_of Bridge.sm_R (thm_C_S7 …) (cor_C_inherits …) (thm_C_soft …) (cor_C_inherits …)
(cor_C_inherits …)` once those rows land. No R parameter remains: `hR` is discharged by `Bridge.sm_R`. -/
theorem corner_laws_and_soft_of (hR : hyp_R) (h7 : VertexEdgeLawC) (hc : CuspLawC) (hs : SoftTheoremC)
    (hrev : ReversalLawC) (htri : TrianglesC) : CornerLawsAndSoftData where
  chamber := prop_C_chamber
  silent := prop_C_silent
  flat := thm_C_S3
  vertex_edge := h7
  triple := hR
  cusp := hc
  empty_cusp := thm_C_S5
  soft := hs
  reversal := hrev
  cyclic := fun _ _ hn P a => cornerStateSum_genericShift hn a P
  triangles := htri

end SM
