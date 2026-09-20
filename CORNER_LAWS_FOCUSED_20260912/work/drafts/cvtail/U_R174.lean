import RProof.X1Rows
import RProof.X1Rows2
import RProof.GenericTransport
import CV.Rounding
import CV.Curl
import CV.UniformRot
import CV.ChamberInvRow
import CV.GroupedKnot
import CV.Axioms
import CV.FullTwist
import CV.HomflyRows
import Bridge.SmR
import SM.ALawful
import SM.CS5
import SM.CS3
import SM.CSilent
import SM.CChamber
import SM.HypR
import SM.RotationReversal

/-! # CV/R tail — FIXED STATEMENTS (judge's FINAL), 2026-09-15

Rows (tools/claims.py): 155 CV:thm:carrierfloor (d3_floor.tex:736-807), 165 CV:singleton_D_i
(d6_vertexedge.tex:2682-2687), 174-178 R:generic_selected / extreme_pair_zero / extreme_transport /
extreme_selected / cv_theorem, 183 Bridge:theorem, 184 SM:corner_laws_and_soft.
Judge, from work/drafts/cvtail/Sketch_A.lean (Architect A, fidelity) and Sketch_B.lean (Architect B,
feasibility).  WINNER: B's skeleton (its SM row-99 interface copy IS the floor lane's FINAL shape; the
consumer corollary `CarrierSlotFloor`; the 165 assembly from a split interface; 175 assembled from the
accepted `PRE_175_*`), with A's GRAFTS (the CV-vocabulary hypothesis class of clause (C) with
`Diagrammatic L`; the two-field row bundle of 165 with the printed "so"; `RowShape`; the flat
11-field final structure following TARGETS' coverage list; the cyclic field discharged now; the
(D) conclusion literal; `(R)`'s polygon field with both regularity proofs).  Decision record:
work/drafts/cvtail/PLAN_FINAL.md.

Check: `cd work/lean && lake env lean ../drafts/cvtail/Statements_FINAL.lean`.  Every `sorry` is
(a) a PLACEHOLDER for a sibling lane's row theorem (`SM.cf_thm_carrierfloor`, `SM.thm_C_S7`,
`SM.thm_C_soft`, `SM.cor_C_inherits`) — deleted when that lane's module lands, (b) a LEAF of the unit
decomposition of PLAN_FINAL.md §6 (frozen statement), or (c) one of the FIXED-NAME R rows 174, 176,
177 (units of this lane, RA arguments).  Everything else is PROVED from accepted declarations.
Nothing here is to be ported before the rows' statement reviews.  Helper prefix of this lane: `cvt_`.

§0 is a VERBATIM copy of the floor lane's interface (work/drafts/floor/Statements_FINAL.lean §2-§6:
`CarrierFloorRData/AData/BData/CHyp/CData`, `Round`, `junctionTemplate`, `AllPosOrOneNeg`,
`UniformOrOneDissent`, `PolygonDiagram.reverse`, `tangencySet`, `CrossesPositively`, `TangencyCount`,
`BClaim`, `zZeroPart`) and of the corner lane's `CS7Data`, `CSoftData`
(work/drafts/corner/Statements_FINAL.lean §4-§5) — to be deleted when those modules land. -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 0.1 SM row 99 cf:thm-carrierfloor — the floor lane's FINAL clause bundles (VERBATIM) -/

structure CarrierFloorRData : Prop where
  P_reverse : ∀ X : Diagram, X.componentCount = 1 → P X.reverse = P X
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → P X'.reverse = P X
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  rot_reverse_polygon : ∀ (X : Diagram) (C : PolyComp), X.Γ = Shadow.single C →
    X.reverse.Γ = Shadow.single C.reverse ∧ rotationNumber C.reverse.P = -rotationNumber C.P
  rot_reverse_curve : ∀ γ : ClosedC1Curve, γ.reverse.rot = -γ.rot

def Round (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε) :
    RoundingWitness C D ε :=
  CornerRounding.roundedWitness h

def junctionTemplate (q u v : Plane) (ε s : ℝ) : Plane :=
  CornerRounding.juncArc (q - ε • u) ε (planeComplex u).arg (principalAngle u v) s

structure CarrierFloorAData : Prop where
  one_record : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h h' : CornerRounding.Admissible C D ε), Round C D ε h = Round C D ε h'
  one_curve : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    (Round C D ε h).Lε = CornerRounding.roundedLoop h
  one_diagram : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    Nonempty (Carried (Round C D ε h).Lε D.toDiagram) ∧
    (Round C D ε h).carried.smoothWrithe = D.toDiagram.writhe
  junction_determined : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ), j < C.k → ∀ s ∈ Set.Icc (0 : ℝ) 1,
    (Round C D ε h).Lε.γ ((Round C D ε h).a j + s * ((Round C D ε h).b j - (Round C D ε h).a j)) =
      junctionTemplate (C.P j) (CornerRounding.uDir C j) (CornerRounding.vDir C j) ε s
  length_determined : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ)
    (h : CornerRounding.Admissible C D ε) (j : ℕ), j < C.k →
    (Round C D ε h).speed * ((Round C D ε h).b j - (Round C D ε h).a j) =
        CornerRounding.juncLen ε (principalTurn C.P j) ∧
    (Round C D ε h).Lε.γ ((Round C D ε h).b j) = C.P j + ε • CornerRounding.vDir C j
  rest_is_L : ∀ (C : PolyComp) (D : PolygonDiagram C) (ε : ℝ) (h : CornerRounding.Admissible C D ε),
    (∀ p : Plane, p ∉ (⋃ i, cornerDisc C ε i) →
      (p ∈ Set.range (Round C D ε h).Lε.γ ↔ p ∈ polygonImage C)) ∧
    ∀ j < C.k, ∀ t ∈ Set.Icc ((Round C D ε h).b j) ((Round C D ε h).a (j + 1)),
      (Round C D ε h).Lε.γ t = (Round C D ε h).Lε.γ ((Round C D ε h).b j) +
        ((Round C D ε h).speed * (t - (Round C D ε h).b j)) • SM.normalize (edge C.P j)

def AllPosOrOneNeg {m : ℕ} (Q : LabelledTuple m) : Prop :=
  (∀ i, 0 < principalTurn Q i) ∨
  (∃ i, principalTurn Q i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn Q j)

def UniformOrOneDissent (C : PolyComp) : Prop :=
  AllPosOrOneNeg C.P ∨ AllPosOrOneNeg (reversal C.P)

def PolygonDiagram.reverse {C : PolyComp} (D : PolygonDiagram C) : PolygonDiagram C.reverse :=
  PolygonDiagram.ofDiagram D.toDiagram.reverse rfl

def tangencySet {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε) (u : Plane) :
    Set ℝ :=
  {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}

def CrossesPositively {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (t : ℝ) : Prop :=
  ∃ j, j < C.k ∧ t ∈ Set.Ioo (W.a j) (W.b j) ∧ 0 < deriv (W.θ j) t

def TangencyCount {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (u : Plane) (R : ℝ) : Prop :=
  (tangencySet W u).Finite ∧ ((tangencySet W u).ncard : ℝ) = R ∧
  ∀ t ∈ tangencySet W u, CrossesPositively W t

def BClaim (C : PolyComp) (D : PolygonDiagram C) : Prop :=
  ∃ (u : Plane) (ε₁ : ℝ), euclideanLength u = 1 ∧ 0 < ε₁ ∧ ε₁ ≤ CornerRounding.clearance C ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ h : CornerRounding.Admissible C D ε,
      TangencyCount (Round C D ε h) u |rotationNumber C.P| ∧
      TangencyCount (Round C D ε h) (-u) |rotationNumber C.P|

structure CarrierFloorBData : Prop where
  tangencies : ∀ (C : PolyComp) (D : PolygonDiagram C), (∀ i, principalTurn C.P i ≠ 0) →
    UniformOrOneDissent C →
    (AllPosOrOneNeg C.P ∧ BClaim C D) ∨ (AllPosOrOneNeg (reversal C.P) ∧ BClaim C.reverse D.reverse)

structure CarrierFloorCHyp (C : PolyComp) (X : Diagram) : Prop where
  shadow : X.Γ = Shadow.single C
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  turn_exists : Regular C.P
  turn_ne : ∀ i, principalTurn C.P i ≠ 0
  turn_lt_pi : ∀ i, |principalTurn C.P i| < Real.pi
  generic : (Shadow.single C).Generic
  alternative : UniformOrOneDissent C

def zZeroPart (f : R) : R :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun e : ℤ × ℤ => e.2 = 0) f.coeff)

theorem coeffAt_zZeroPart_zero (f : R) (d : ℤ) : coeffAt d 0 (zZeroPart f) = coeffAt d 0 f := by
  simp [zZeroPart, coeffAt]

structure CarrierFloorCData : Prop where
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  floor_zZero : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X → zZeroPart (P X) ≠ 0 →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (zZeroPart (P X)) : ℝ)

structure CarrierFloorData : Prop where
  clauseR : CarrierFloorRData
  clauseA : CarrierFloorAData
  clauseB : CarrierFloorBData
  clauseC : CarrierFloorCData

/-- PLACEHOLDER for the floor lane's row 99 (`SM.cf_thm_carrierfloor :=
cf_thm_carrierfloor_of_bound (transverseFrontBound_of_fdContactShape ⟨…⟩)` once row 94 lands). -/
theorem cf_thm_carrierfloor : CarrierFloorData := by
  sorry

end

end SM

/-! ## 0.2 The corner lane's FINAL bundles of rows 110 thm:C-S7 and 112 thm:C-soft (VERBATIM,
work/drafts/corner/Statements_FINAL.lean §4-§5; the genericity of the halves / of `P_ε` is
UNIVERSALLY quantified there) — and PLACEHOLDERS for the fixed-name rows. -/

namespace SM

open WallGerm SoftDuplication

structure CS7Data : Prop where
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n)
    (h : g.VertexEdgeAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)),
    ∀ tp tm : g.SideParameter,
      cornerStateSum hn (g.sideTuple true tp).property -
          cornerStateSum hn (g.sideTuple false tm).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂)

structure CSoftData : Prop where
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ hQ : Generic (softInsertion P j q ε),
      (cornerStateSum (by omega : 3 ≤ n + 1) hQ : ℚ) =
        softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

/-- PLACEHOLDER for the corner lane's row 110 (FIXED name; `thm_C_S7_of_floor thm_floor`). -/
theorem thm_C_S7 : CS7Data := by
  sorry

/-- PLACEHOLDER for the corner lane's row 112 (FIXED name; `thm_C_soft_of_floor thm_floor`). -/
theorem thm_C_soft : CSoftData := by
  sorry

end SM

/-! ## 1. Row 155 CV:thm:carrierfloor (d3_floor.tex:736-807) — the CV statement

Clauses (R)(A)(B)(C) are the SM row-99 clauses word for word (rule F6), stated on CV's printed binders
through the accepted polygon bridge of CV/Rounding.lean §1 (`polyComp L hreg`, `OverUnder`,
`toPolygonDiagram`, `roundingRecord`, `clearance`) exactly as the accepted CV:lem:rounding was; `rot`
is CV:def:rot's `rot`/`rotAbs` (`rot_eq_rotationNumber`), the curve `rot` is `rotCurve`, `P_D` is
CV:def:homfly's `homfly` (`P_eq_homfly`).  They are PROVED from the SM bundles by the conditional
theorems `carrierfloor_*_of_sm` (D-F11 pattern).  Clause (D) is CV-only and PROVED here.  Readings
FR-CV-155-1 … 155-9 in PLAN_FINAL.md §3. -/

namespace CV

open SM SM.Link SM.Carrier SM.GeoCarrier
open scoped ContDiff

noncomputable section
open Classical

/-- "either every principal turn is positive, or exactly one is negative [and every other is
positive]" in CV's vocabulary (`CV.principalTurn`, definitionally SM's: `principalTurn_eq_sm`). -/
def AllPosOrOneNegCV {c : ℕ} (L : LabelledTuple c) : Prop :=
  (∀ i, 0 < principalTurn L i) ∨
  (∃ i, principalTurn L i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn L j)

/-- "after reversing the orientation of L if necessary, …" — the literal reversal form of the floor
lane (FR-FL-B1/F1); reversal negates every principal turn (`principalTurn_reversal`). -/
def UniformOrOneDissentCV {c : ℕ} (L : LabelledTuple c) : Prop :=
  AllPosOrOneNegCV L ∨ AllPosOrOneNegCV (reversal L)

/-- F6 sanity: the CV alternative IS the SM alternative of the bridged polygon (`Iff.rfl`). -/
theorem uniformOrOneDissentCV_iff_sm {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) :
    UniformOrOneDissentCV L ↔ SM.UniformOrOneDissent (polyComp L hreg) := Iff.rfl

/-- **(R)** "Let K be an oriented knot and −K the same knot with its orientation reversed. Then
P_{−K} = P_K. Moreover a diagram of −K obtained by reversing the orientation of a diagram of K has the
same crossing signs, the same writhe, and rotation number of the underlying plane curve negated"
(d3:739-743); `P_K = homfly` (CV:def:homfly), "rot as in Definition def:rot" (`CV.rot` on the polygon
of a polygonal diagram, `CV.rotCurve` on a C¹ curve). -/
structure CarrierFloorRData : Prop where
  /-- "P_{−K} = P_K" on a diagram `X` of `K` -/
  homfly_reverse : ∀ X : Diagram, X.componentCount = 1 → homfly X.reverse = homfly X
  /-- "P_{−K} = P_K" for any two diagrams `X`, `X'` of the knot `K` (`LinkEquiv` class, D2) -/
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → homfly X'.reverse = homfly X
  /-- "the same crossing signs" -/
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  /-- "the same writhe" -/
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  /-- "rotation number of the underlying plane curve negated" — polygonal diagram: the underlying
  curve of `X` is the polygon `L`, that of the reversed diagram is the reversed polygon, and CV:def:rot's
  `rot` is negated (the accepted `CV.rot_reversal`) -/
  rot_reverse_polygon : ∀ (X : Diagram) {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L)
    (hL' : Regular (reversal L)), X.Γ = Shadow.single (polyComp L hL) →
    X.reverse.Γ = Shadow.single (polyComp L hL).reverse ∧ rot (reversal L) hL' = -rot L hL
  /-- — C¹ regular curve: CV:def:rot's `rot(γ) = tw(T_γ)` is negated -/
  rot_reverse_curve : ∀ γ : ClosedC1Curve, rotCurve γ.reverse = -rotCurve γ

/-- The record `Round(L, D, ε)` on CV's binders is the accepted `roundingRecord`
(= `SM.Round (polyComp L hreg) (D.toPolygonDiagram hL) ε (roundingAdmissible …)` by `rfl`). -/
abbrev Rnd {n : ℕ} [NeZero n] {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε :=
  roundingRecord hL hreg hturn D hε hε₀

/-- **(A)** "Let L and D satisfy the hypotheses of Lemma lem:rounding. For every ε ∈ (0, ε₀(L)), the
construction in the proof of that lemma returns one curve and one diagram at those data: the junction
inserted at the corner q_i is determined by ε, by the two incident unit directions and by the
transition profile, which is fixed once and for all …; the arc length ℓ is then determined by the
endpoint condition, and the rest of the curve is L itself. Write Round(L,D,ε) = (L_ε, D_ε)"
(d3:745-760): the floor lane's six fields at `C := polyComp L hreg`, `D := D.toPolygonDiagram hL`,
`Round := roundingRecord`. -/
structure CarrierFloorAData : Prop where
  /-- "one curve and one diagram at those data" — one record, the named construction -/
  one_record : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    Rnd hL hreg hturn D hε hε₀ =
      SM.Round (polyComp L hreg) (D.toPolygonDiagram hL) ε (roundingAdmissible hL hreg hturn D hε hε₀)
  /-- — the curve is the named construction -/
  one_curve : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    (Rnd hL hreg hturn D hε hε₀).Lε = CornerRounding.roundedLoop (roundingAdmissible hL hreg hturn D hε hε₀)
  /-- — the diagram `D_ε` is `D` itself, carried, with its data inherited -/
  one_diagram : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    Nonempty (Carried (Rnd hL hreg hturn D hε hε₀).Lε (D.toPolygonDiagram hL).toDiagram) ∧
    (Rnd hL hreg hturn D hε hε₀).carried.smoothWrithe = (D.toPolygonDiagram hL).toDiagram.writhe
  /-- "the junction inserted at the corner q_i is determined by ε, by the two incident unit directions
  and by the transition profile, which is fixed once and for all" (parametrically, FR-FL-A1) -/
  junction_determined : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) (j : ℕ), j < n → ∀ s ∈ Set.Icc (0 : ℝ) 1,
    (Rnd hL hreg hturn D hε hε₀).Lε.γ ((Rnd hL hreg hturn D hε hε₀).a j +
        s * ((Rnd hL hreg hturn D hε hε₀).b j - (Rnd hL hreg hturn D hε hε₀).a j)) =
      SM.junctionTemplate (L j) (CornerRounding.uDir (polyComp L hreg) j)
        (CornerRounding.vDir (polyComp L hreg) j) ε s
  /-- "the arc length ℓ is then determined by the endpoint condition" -/
  length_determined : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) (j : ℕ), j < n →
    (Rnd hL hreg hturn D hε hε₀).speed * ((Rnd hL hreg hturn D hε hε₀).b j - (Rnd hL hreg hturn D hε hε₀).a j) =
        CornerRounding.juncLen ε (principalTurn L j) ∧
    (Rnd hL hreg hturn D hε hε₀).Lε.γ ((Rnd hL hreg hturn D hε hε₀).b j) =
      L j + ε • CornerRounding.vDir (polyComp L hreg) j
  /-- "and the rest of the curve is L itself" (the accepted `CV.rounding.a` on the record) -/
  rest_is_L : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    (∀ p : Plane, p ∉ (⋃ i, cornerDisc (polyComp L hreg) ε i) →
      (p ∈ Set.range (Rnd hL hreg hturn D hε hε₀).Lε.γ ↔ p ∈ ⋃ i : ZMod n, edgeSegment L i)) ∧
    ∀ j < n, ∀ t ∈ Set.Icc ((Rnd hL hreg hturn D hε hε₀).b j) ((Rnd hL hreg hturn D hε hε₀).a (j + 1)),
      (Rnd hL hreg hturn D hε hε₀).Lε.γ t = (Rnd hL hreg hturn D hε hε₀).Lε.γ ((Rnd hL hreg hturn D hε hε₀).b j) +
        ((Rnd hL hreg hturn D hε hε₀).speed * (t - (Rnd hL hreg hturn D hε hε₀).b j)) • normalize (edge L j)

/-- Clause (B)'s claim on CV's binders: "there are a direction u ∈ S¹ and an ε₁ > 0 such that for every
ε ∈ (0, ε₁) the rounded curve L_ε of the record Round(L,D,ε) from clause (A) has exactly R points at
which its unit tangent equals u and exactly R at which it equals −u; at each of them the tangent
crosses that direction in the positive sense", `R = |rot(L)| = rotAbs L hreg` (CV:def:rot);
`ε₁ ≤ ε₀(L)` so that the record exists (the printed proof takes `ε₁ = ε₀(L)`, FR-FL-B4). -/
def BClaimCV {n : ℕ} [NeZero n] {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) : Prop :=
  ∃ (u : Plane) (ε₁ : ℝ) (_hu : euclideanLength u = 1) (_hpos : 0 < ε₁) (hle : ε₁ ≤ clearance L hreg),
    ∀ (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < ε₁),
      SM.TangencyCount (Rnd hL hreg hturn D hε (hε₁.trans_le hle)) u (rotAbs L hreg) ∧
      SM.TangencyCount (Rnd hL hreg hturn D hε (hε₁.trans_le hle)) (-u) (rotAbs L hreg)

/-- **(B)** "Let L be a diagrammatic closed polygon whose principal turns all exist and are nonzero,
carrying a diagram D, and assume, after reversing the orientation of L if necessary, that either every
principal turn is positive, or exactly one is negative. Put R = |rot(L)|. Then …" (d3:761-776).  The
claim is made for the polygon in the normalised orientation ("perform the allowed normalization once",
FR-FL-B1: for an all-negative `L` the tangent crosses `u` in the NEGATIVE sense): for `L` itself when `L`
is already positive-majority, for `−L` carrying `−D` otherwise — the reversal branch on the bridge's SM
objects (`OverUnder.reverse` is not library material, FR-CV-155-5). -/
structure CarrierFloorBData : Prop where
  tangencies : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)),
    UniformOrOneDissentCV L →
    (AllPosOrOneNegCV L ∧ BClaimCV hL hreg hturn D) ∨
    (AllPosOrOneNegCV (reversal L) ∧
      SM.BClaim (polyComp L hreg).reverse (D.toPolygonDiagram hL).reverse)

/-- The hypotheses of **(C)** (d3:777-795), one item per printed clause, on the oriented knot diagram `X`
"whose underlying plane curve is a closed polygon L" (`shadow`), "all of whose crossings are positive"
(`positive`), "with all principal turns existing" (the parameter `hreg : Regular L`), "nonzero"
(`turn_ne`), "and of magnitude below π" (`turn_lt_pi`), "with finitely many double points, all
transversal, with no triple points, none of them a corner of L, and no corner of L lying on a
non-incident edge" — in CV's vocabulary this list IS CV:def:diagrammatic ("The no-triple condition
repeats the shared-image clause of Definition def:diagrammatic"; `diagrammatic`), and "after reversing
the orientation if necessary … either every principal turn is positive, or exactly one is negative and
every other is positive" (`alternative`).  Bridged to SM's seven-field class by `toSM`. -/
structure CarrierFloorCHyp {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) (X : Diagram) :
    Prop where
  shadow : X.Γ = Shadow.single (polyComp L hreg)
  positive : ∀ x : X.Γ.Crossing, X.IsPositive x
  diagrammatic : Diagrammatic L
  turn_ne : ∀ i, principalTurn L i ≠ 0
  turn_lt_pi : ∀ i, |principalTurn L i| < Real.pi
  alternative : UniformOrOneDissentCV L

/-- CV's hypothesis class is SM's at the bridged polygon: the double-point list is the genericity of
the one-polygon shadow (`single_generic_of_diagrammatic`), "principal turns exist" is `Regular`
(`regular_iff_sm`); the turn fields are definitionally SM's (`principalTurn_eq_sm`). PROVED. -/
theorem CarrierFloorCHyp.toSM {n : ℕ} [NeZero n] {L : LabelledTuple n} {hreg : Regular L} {X : Diagram}
    (h : CarrierFloorCHyp L hreg X) : SM.CarrierFloorCHyp (polyComp L hreg) X where
  shadow := h.shadow
  positive := h.positive
  turn_exists := (regular_iff_sm L).mp hreg
  turn_ne := h.turn_ne
  turn_lt_pi := h.turn_lt_pi
  generic := single_generic_of_diagrammatic h.diagrammatic hreg
  alternative := h.alternative

/-- **(C)** "Then min deg_a P_D(a,z) ≥ 1 − w − R (eq:floor), and the same bound holds for
f_D(a) = [z^0]P_D(a,z) whenever f_D ≠ 0" (d3:796-801); `w = X.writhe`, `R = rotAbs L hreg` (in `ℤ`,
CV:def:rot's integer `R(L)`; SM's is the real `|rot|`, FR-CV-155-6), `P_D = homfly X`; `f_D` is the
floor lane's `zZeroPart` (FR-FL-C3); the support form is the corollary `floor_z0`. -/
structure CarrierFloorCData : Prop where
  floor : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) (X : Diagram),
    CarrierFloorCHyp L hreg X → 1 - X.writhe - (rotAbs L hreg : ℤ) ≤ mindegAZ (homfly X)
  floor_zZero : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) (X : Diagram),
    CarrierFloorCHyp L hreg X → SM.zZeroPart (homfly X) ≠ 0 →
    1 - X.writhe - (rotAbs L hreg : ℤ) ≤ mindegAZ (SM.zZeroPart (homfly X))

/-- `homfly X ≠ 0` (lp:core, `P_ne_zero`, `P_eq_homfly`). -/
theorem cvt_homfly_ne_zero (X : Diagram) : homfly X ≠ 0 := by
  rw [← P_eq_homfly]; exact P_ne_zero X

/-- The support form of (C) ("every monomial `a^d z^0` present in `P_D` has `d ≥ 1 − w − R`"; the form
the R consumers read): a corollary of `floor` by `mindegAZ_spec`. PROVED. -/
theorem CarrierFloorCData.floor_z0 (h : CarrierFloorCData) {n : ℕ} [NeZero n] (L : LabelledTuple n)
    (hreg : Regular L) (X : Diagram) (hX : CarrierFloorCHyp L hreg X) (d : ℤ)
    (hd : coeffAt d 0 (homfly X) ≠ 0) : 1 - X.writhe - (rotAbs L hreg : ℤ) ≤ d :=
  le_trans (h.floor L hreg X hX) ((mindegAZ_spec (cvt_homfly_ne_zero X)).2 d 0 hd)

/-- **(D)** "Let P be generic, let S ∈ Ind(G_P) and let L be a carrier of S carrying no residual piece,
so that P_{S,L} = 1 and w_{S,L} = 0 by Definition def:X1's empty conventions …, and suppose that all its
principal turns are nonzero and that, after reversing the orientation if necessary, either every turn is
positive or exactly one is negative. Then R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥ 1 − w_{S,L} − R(L)"
(d3:802-807), on CV:def:X1's accepted objects; the turns are those of the carrier's corner polygon
(CV:def:wind / CV:def:rot).  The "so that" is commentary on the hypothesis (the accepted
`X1_definition.empty_conventions`), not a conclusion (FR-CV-155-7). -/
structure CarrierFloorDData : Prop where
  floor_D : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    piecesOn hG.crossingGeometry S q = ∅ →
    (∀ j, principalTurn (geoCornerPolygon hG.crossingGeometry S q) j ≠ 0) →
    UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q) →
    1 ≤ carrierR hn hG hS q ∧ mindegAZ (groupedPoly hn hG hS q) = 0 ∧
      1 - groupedWrithe hG q - (carrierR hn hG hS q : ℤ) ≤ 0

/-- **Row 155** (proposed row declaration `CV.carrierfloor : CarrierFloorData`): the five printed clauses. -/
structure CarrierFloorData : Prop where
  clauseR : CarrierFloorRData
  clauseA : CarrierFloorAData
  clauseB : CarrierFloorBData
  clauseC : CarrierFloorCData
  clauseD : CarrierFloorDData

/-! ### 1.1 Clause (D) — PROVED NOW (CV:lem:uniformrot + def:X1's empty conventions) -/

/-- `|rot L| ≥ 1` under the alternative: uniformrot (i) in the uniform case, (ii) in the one-dissent
case, after reversal (`rot_reversal`) when the normalised orientation is the reversed one. -/
theorem cvt_one_le_rotAbs_of_alt {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L)
    (halt : UniformOrOneDissentCV L) : 1 ≤ rotAbs L hL := by
  have key : (1 : ℤ) ≤ |rot L hL| := by
    rcases halt with h | h
    · rcases h with hpos | ⟨a, hneg, hoth⟩
      · exact (uniformrot.pos_ge_one c L hL hpos).trans (le_abs_self _)
      · exact (uniformrot.one_dissent c L hL a hneg (fun i hi => (hoth i hi).le)).2.trans (le_abs_self _)
    · have hL' := regular_reversal' hL
      have hr : rot (reversal L) hL' = -rot L hL := rot_reversal hL hL'
      rcases h with hpos | ⟨a, hneg, hoth⟩
      · have := uniformrot.pos_ge_one c _ hL' hpos
        rw [hr] at this
        rw [abs_eq_neg_self.mpr (by linarith)]; exact this
      · have := (uniformrot.one_dissent c _ hL' a hneg (fun i hi => (hoth i hi).le)).2
        rw [hr] at this
        rw [abs_eq_neg_self.mpr (by linarith)]; exact this
  have : (1 : ℤ) ≤ (rotAbs L hL : ℤ) := by rw [rotAbs_cast]; exact key
  exact_mod_cast this

theorem cvt_mindegAZ_one : mindegAZ (1 : R) = 0 := by
  refine mindegAZ_eq_of_spec ⟨0, ?_⟩ fun d' k h => ?_
  · rw [coeffAt_one]; simp
  · rw [coeffAt_one] at h
    split_ifs at h with hh
    · exact (Prod.mk.inj hh).1.le
    · exact absurd rfl h

/-- **Row 155 (D)**, PROVED. -/
theorem carrierfloor_D : CarrierFloorDData where
  floor_D := by
    intro n _ hn P hG S hS q hempty _ halt
    have hR := cvt_one_le_rotAbs_of_alt _ (carrierPolygon_cvRegular hn hG hS q) halt
    refine ⟨hR, ?_, ?_⟩
    · rw [groupedPoly_of_piecesOn_eq_empty hn hG hS q hempty]; exact cvt_mindegAZ_one
    · rw [groupedWrithe_of_piecesOn_eq_empty hG q hempty]
      have : (1 : ℤ) ≤ (carrierR hn hG hS q : ℤ) := by exact_mod_cast hR
      omega

/-! ### 1.2 Clauses (R)(A)(B)(C) from SM row 99 through the bridge (D-F11 conditional theorems) -/

/-- (R): `P = homfly` (lp:core); the polygon clause is the SM shadow clause plus the accepted
`CV.rot_reversal`. PROVED. -/
theorem carrierfloor_R_of_sm (h : SM.CarrierFloorRData) : CarrierFloorRData where
  homfly_reverse := fun X hc => by rw [← P_eq_homfly, ← P_eq_homfly]; exact h.P_reverse X hc
  knot_reverse := fun X X' hc he => by rw [← P_eq_homfly, ← P_eq_homfly]; exact h.knot_reverse X X' hc he
  sign_reverse := h.sign_reverse
  writhe_reverse := h.writhe_reverse
  rot_reverse_polygon := by
    intro X c _ L hL hL' hX
    exact ⟨(h.rot_reverse_polygon X (polyComp L hL) hX).1, rot_reversal hL hL'⟩
  rot_reverse_curve := fun γ => h.rot_reverse_curve γ

/-- (A): SM's fields at `polyComp L hreg`, `D.toPolygonDiagram hL` (`Rnd … = Round …` is `rfl`;
`(polyComp L hreg).P = L` is `rfl`); `rest_is_L` is the accepted `CV.rounding.a` on the record. PROVED. -/
theorem carrierfloor_A_of_sm (h : SM.CarrierFloorAData) : CarrierFloorAData where
  one_record := fun _ _ _ _ _ _ _ _ => rfl
  one_curve := fun L hL hreg hturn D ε hε hε₀ =>
    h.one_curve (polyComp L hreg) (D.toPolygonDiagram hL) ε (roundingAdmissible hL hreg hturn D hε hε₀)
  one_diagram := fun L hL hreg hturn D ε hε hε₀ =>
    h.one_diagram (polyComp L hreg) (D.toPolygonDiagram hL) ε (roundingAdmissible hL hreg hturn D hε hε₀)
  junction_determined := fun L hL hreg hturn D ε hε hε₀ j hj s hs =>
    h.junction_determined (polyComp L hreg) (D.toPolygonDiagram hL) ε
      (roundingAdmissible hL hreg hturn D hε hε₀) j hj s hs
  length_determined := fun L hL hreg hturn D ε hε hε₀ j hj =>
    h.length_determined (polyComp L hreg) (D.toPolygonDiagram hL) ε
      (roundingAdmissible hL hreg hturn D hε hε₀) j hj
  rest_is_L := fun L hL hreg hturn D ε hε hε₀ =>
    rounding.a L hL hreg D ε (roundingRecord hL hreg hturn D hε hε₀)

/-- `|rot(L)|` in CV's integer form is `|rotationNumber L|` (accepted `rotAbs_cast`,
`rot_eq_rotationNumber`). -/
theorem rotAbs_intCast_real {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) :
    ((rotAbs L hreg : ℤ) : ℝ) = |rotationNumber L| := by
  rw [rotAbs_cast, Int.cast_abs, rot_eq_rotationNumber hreg]

/-- (B): SM's normalised-orientation disjunction at the bridge; the counts read `R = rotAbs L hreg`. PROVED. -/
theorem carrierfloor_B_of_sm (h : SM.CarrierFloorBData) : CarrierFloorBData where
  tangencies := by
    intro n _ L hL hreg hturn D halt
    rcases h.tangencies (polyComp L hreg) (D.toPolygonDiagram hL) hturn halt with ⟨hpos, hB⟩ | ⟨hpos, hB⟩
    · left
      refine ⟨hpos, ?_⟩
      obtain ⟨u, ε₁, hu, hε₁, hle, hall⟩ := hB
      refine ⟨u, ε₁, hu, hε₁, hle, fun ε hε hε₁' => ?_⟩
      have key : ((rotAbs L hreg : ℕ) : ℝ) = |rotationNumber (polyComp L hreg).P| := by
        show ((rotAbs L hreg : ℕ) : ℝ) = |rotationNumber L|
        have := rotAbs_intCast_real L hreg
        exact_mod_cast this
      rw [key]
      exact hall ε hε hε₁' (roundingAdmissible hL hreg hturn D hε (hε₁'.trans_le hle))
    · exact Or.inr ⟨hpos, hB⟩

/-- (C): SM's (C) at the bridge (`P = homfly`, `R = rotAbs`, hypotheses by `toSM`). PROVED. -/
theorem carrierfloor_C_of_sm (h : SM.CarrierFloorCData) : CarrierFloorCData where
  floor := by
    intro n _ L hreg X hX
    have := h.floor _ X hX.toSM
    have hR : |rotationNumber (polyComp L hreg).P| = ((rotAbs L hreg : ℤ) : ℝ) :=
      (rotAbs_intCast_real L hreg).symm
    rw [P_eq_homfly, hR] at this
    exact_mod_cast this
  floor_zZero := by
    intro n _ L hreg X hX hne
    have := h.floor_zZero _ X hX.toSM (by rwa [P_eq_homfly])
    have hR : |rotationNumber (polyComp L hreg).P| = ((rotAbs L hreg : ℤ) : ℝ) :=
      (rotAbs_intCast_real L hreg).symm
    rw [P_eq_homfly, hR] at this
    exact_mod_cast this

/-- **Row 155 from SM row 99** (conditional, D-F11; library material): the row theorem is this applied to
the floor lane's `SM.cf_thm_carrierfloor`. PROVED. -/
theorem carrierfloor_of_sm (h : SM.CarrierFloorData) : CarrierFloorData where
  clauseR := carrierfloor_R_of_sm h.clauseR
  clauseA := carrierfloor_A_of_sm h.clauseA
  clauseB := carrierfloor_B_of_sm h.clauseB
  clauseC := carrierfloor_C_of_sm h.clauseC
  clauseD := carrierfloor_D

/-- **Row 155, CV:thm:carrierfloor** (proposed name `CV.carrierfloor`; declared and mapped only when
row 99 lands, D-F11/D-F14). -/
theorem carrierfloor : CarrierFloorData := carrierfloor_of_sm SM.cf_thm_carrierfloor

/-! ### 1.3 The consumer corollary of (C)+(D): the carrier floor in def:X1's symbols (library, not a row).
Rows 165, 174, 176, 177 consume ONLY this: "thm:carrierfloor (C) applies to each loop as a carrier of S′
— through cor:groupedknot (B) if it bears a piece and thm:carrierfloor (D) if it does not"
(d6:2936-2939; GSC §4, EST (16), ESC (19)).  Stated as the printed eq:floor (`slot ≤ mindeg_a P_{S,L}`);
its support form ("no exponent below the slot occurs in `f_L`") is the corollary `coeff_zero`. -/

/-- The carrier floor in def:X1's symbols, for every carrier of a CV-generic polygon that is uniform or
one-dissent after reversal. -/
def CarrierSlotFloor : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q) →
    slot hn hG hS q ≤ mindegAZ (groupedPoly hn hG hS q)

/-- `P_{S,L} ≠ 0` (cor:groupedknot (B) + lp:core when a piece is carried; `1 ≠ 0` otherwise). PROVED. -/
theorem cvt_groupedPoly_ne_zero {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    groupedPoly hn hG hS q ≠ 0 := by
  by_cases h : (piecesOn hG.crossingGeometry S q).Nonempty
  · rw [← ((groupedknot hn hG hS q).grouped_polynomial h).1]
    exact cvt_homfly_ne_zero _
  · rw [groupedPoly_of_piecesOn_eq_empty hn hG hS q (Finset.not_nonempty_iff_eq_empty.mp h)]
    exact one_ne_zero

/-- Knot parity of a grouped polynomial: `P_{S,L} ∈ ℤ[a^{±1}, z²]` (cor:groupedknot (B) + ax:homfly's
`knot_parity`; `InSupportM.one` when piece-free). PROVED (for the RA units' knot-parity steps). -/
theorem cvt_groupedPoly_inSupportM {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    InSupportM 1 (groupedPoly hn hG hS q) := by
  by_cases h : (piecesOn hG.crossingGeometry S q).Nonempty
  · rw [← ((groupedknot hn hG hS q).grouped_polynomial h).1]
    exact ax_homfly.knot_parity _ ((groupedknot hn hG hS q).knot_diagram h).1
  · rw [groupedPoly_of_piecesOn_eq_empty hn hG hS q (Finset.not_nonempty_iff_eq_empty.mp h)]
    exact InSupportM.one

/-- "no exponent below the slot occurs in `f_L = [z⁰] P_{S,L}`" — the support form the RA texts invoke. PROVED. -/
theorem CarrierSlotFloor.coeff_zero (hF : CarrierSlotFloor) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {P : LabelledTuple n} (hG : Generic P) {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S)
    (halt : UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q)) (d : ℤ)
    (hd : coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0) : slot hn hG hS q ≤ d :=
  le_trans (hF hn hG hS q halt) ((mindegAZ_spec (cvt_groupedPoly_ne_zero hn hG hS q)).2 d 0 hd)

/-- LEAF (unit U-SLOT). Route: piece-free carrier — clause (D) (`groupedPoly = 1`, `mindegAZ 1 = 0 ≥ slot`);
carrier with pieces — cor:groupedknot (B) (`carrierDiagram` is a positive knot diagram on
`geoCornerPolygon` with `homfly = groupedPoly`, `writhe = groupedWrithe`, no triple points),
`geoCarrierShadow = Shadow.single (geoCarrierPolyComp …)` (`geoPositiveLift_Γ`), turns nonzero
(`geoCornerPolygon_turn_ne_zero`), `|turn| < π` (`principalAngle_bounds`), the alternative
(`principalTurn_eq_sm`, `Iff.rfl`), SM's `CarrierFloorCHyp.of_diagram`-style assembly; then SM (C)'s
`floor` with `rot_eq_rotationNumber`, `rotAbs_cast`, `carrierR_cast`. -/
theorem carrier_slot_floor_of_C (hC : SM.CarrierFloorCData) : CarrierSlotFloor := by
  sorry

/-! ## 2. Row 165 CV:singleton_D_i — thm:s7universal (D)(i) (d6_vertexedge.tex:2682-2687)

"(i) Let S ∈ Ind(G_P), let A be a uniform carrier of S, and let {c} be a singleton residual piece of S
carried by A. Then min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2, so the factor Ω₁(S,A) of Definition def:X1
is zero."  `f_A = [z^0] P_{S,A}` (def:markeddata), `P_{S,A} = groupedPoly`, `1 − w_{S,A} − R(A) = slot`,
`Ω₁(S,A) = Omega1` (CV:def:X1); "uniform carrier" = CV:def:wind's `CarrierUniform`; the degree bound in
support form (every `a^d z^0` present has `d ≥ slot + 2`; vacuous when `f_A = 0`, FR-CV-165-1). -/

/-- "`{c}` a singleton residual piece of `S` carried by `A`": `c ∈ U(S)`, its piece has label set `{c}`,
and that piece is assigned to `q` (def:X1 / lem:carriers (iv)) — exactly the shape produced by the
accepted `ExtremePairZeroData.third_singleton_piece` (FR-CV-165-2). -/
structure SingletonPieceOn {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (q : GeoComponent hP S) (c : Crossing P) : Prop where
  mem_U : c ∈ U hP S
  labels : pieceLabels hP S (pieceOf hP S c mem_U) = {c}
  owner : pieceOf hP S c mem_U ∈ piecesOn hP S q

/-- **Row 165** (proposed row declaration `CV.singleton_D_i : SingletonDiData`), the two printed clauses. -/
structure SingletonDiData : Prop where
  /-- "min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2" -/
  degree_gap : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
      ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d
  /-- "so the factor Ω₁(S,A) of Definition def:X1 is zero" -/
  factor_zero : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c → Omega1 hn hG hS q = 0

/-- The printed "so": the coefficient at the slot lies two degrees below the lowest present degree. PROVED. -/
theorem cvt_omega1_eq_zero_of_gap {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hgap : ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) :
    Omega1 hn hG hS q = 0 := by
  by_contra hne
  have := hgap (slot hn hG hS q) hne
  omega

/-- The bundle from its first clause. PROVED. -/
theorem SingletonDiData.of_degree_gap
    (hgap : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
      {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
      CarrierUniform hG.crossingGeometry S q →
      ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
        ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) :
    SingletonDiData where
  degree_gap := hgap
  factor_zero := by
    intro n _ hn P hG S hS q hq c hc
    exact cvt_omega1_eq_zero_of_gap hn hG hS q (hgap hn hG hS q hq c hc)

/-- The split interface (unit U-SPLIT of THIS lane, on the geo layer — the corner lane's cb:singleton
split `sg_daughters_*` lives on SM's `Component`/`IsDecomposition`, so it cannot be consumed here,
FR-CV-165-3): smoothing `c` splits the uniform carrier `A` of `S` into two carriers `Λ₁, Λ₂` of
`S' = S ∪ {c}` with `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}` (the pieces "literally the same objects" +
`P_{{c}} = 1`), `w_{S,A} = w_{S',Λ₁} + w_{S',Λ₂} + 1`, `R(A) = R(Λ₁) + R(Λ₂)` (turnlift (ii) +
uniformrot signs), one loop uniform and the other one-dissent (d6:2890-2935). -/
def SingletonSplitData : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
      ∃ hS' : insert c S ∈ Ind hG.crossingGeometry,
      ∃ q₁ q₂ : GeoComponent hG.crossingGeometry (insert c S),
        groupedPoly hn hG hS q = groupedPoly hn hG hS' q₁ * groupedPoly hn hG hS' q₂ ∧
        groupedWrithe hG q = groupedWrithe hG q₁ + groupedWrithe hG q₂ + 1 ∧
        (carrierR hn hG hS q : ℤ) = carrierR hn hG hS' q₁ + carrierR hn hG hS' q₂ ∧
        UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert c S) q₁) ∧
        UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert c S) q₂)

/-- **Row 165 from the split and the carrier floor** (the printed proof d6:2890-2947; the two floors add
through `mindegAZ_mul` on the nonzero factors — the corner lane's FR-CC-3 route, FR-CV-165-4). PROVED. -/
theorem singleton_D_i_of (hsplit : SingletonSplitData) (hfloor : CarrierSlotFloor) : SingletonDiData := by
  refine SingletonDiData.of_degree_gap ?_
  intro n _ hn P hG S hS q hq c hc d hd
  · obtain ⟨hS', q₁, q₂, hpoly, hwrithe, hrot, halt₁, halt₂⟩ := hsplit hn hG hS q hq c hc
    have h₁ := hfloor hn hG hS' q₁ halt₁
    have h₂ := hfloor hn hG hS' q₂ halt₂
    have hne₁ := cvt_groupedPoly_ne_zero hn hG hS' q₁
    have hne₂ := cvt_groupedPoly_ne_zero hn hG hS' q₂
    rw [hpoly] at hd
    have hle := (mindegAZ_spec (mul_ne_zero hne₁ hne₂)).2 d 0 hd
    rw [mindegAZ_mul hne₁ hne₂] at hle
    unfold slot at h₁ h₂ ⊢
    rw [hwrithe, hrot]
    omega

/-- LEAF (unit U-SPLIT, ~1.5-2.5k lines): the split interface on the geo layer. -/
theorem cvt_singleton_split : SingletonSplitData := by
  sorry

/-- **Row 165, CV:singleton_D_i** (proposed name `CV.singleton_D_i`; declared and mapped only when
row 99 (C) lands). -/
theorem singleton_D_i : SingletonDiData :=
  singleton_D_i_of cvt_singleton_split (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC)

end

end CV

/-! ## 3. Rows 174-178 — the FIXED statements (RProof/X1Rows.lean's bundles in the accepted row shape)
and the PROVED assembly of row 178. -/

namespace RProof

open SM SM.GeoCarrier

/-- The fixed shape of an X₁-dependent R row (the accepted siblings' signature: `exterior`
X1Rows2.lean:1966, `availability_zero_one` :3619, `generic_selector` X1Rows.lean:1309,
`generic_transport` GenericTransport.lean:11157). -/
def RowShape (D : ∀ {n : ℕ} [NeZero n], 3 ≤ n → CV.Event n → ZMod n → ZMod n → ZMod n → ℝ → Prop) :
    Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g → ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ D hn E e f g δ

theorem rowShape_170 : RowShape @AvailabilityZeroOneData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => availability_zero_one hn E e f g h3 h4e h4f h4g hE
theorem rowShape_172 : RowShape @GenericSelectorData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_selector hn E e f g h3 h4e h4f h4g hE
theorem rowShape_173 : RowShape @GenericTransportData :=
  fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_transport hn E e f g h3 h4e h4f h4g hE

variable {n : ℕ} [NeZero n]

/-! ## Unit U-174 (prefix `gsc_`) — the generic selected complementary couple
(R_GENERIC_SELECTED_COUPLE_PROOF.md, (GSC) `T_E(b) = T_P(b) + T_P(ac)`)

Pattern D-F11: the Reidemeister move and the diagram identifications the RA argument needs are stated
as explicit interface Props (`gsc_fulltwist_triple` — the G10 RII deletion of the switched empty pair
`a, c`; `gsc_smoothing_split` — the two-component smoothing carries the pair-row records; the bundle
`gsc_Ledger` — the carrier/selector/rotation ledger of GSC §1–§3; the event-level interface
`gsc_moves`), the RA ledger of GSC §4–§5 is PROVED from them and from `CV.CarrierSlotFloor`
(`gsc_ledger : gsc_moves → CV.CarrierSlotFloor → RowShape @GenericSelectedData`), and the moves are
realised as far as the accepted library allows (`gsc_wall_of_endpoint`, `gsc_Ind_*`, the sign
facts; see U_R174_REPORT.md for what remains).  Nothing here is mapped; the interface Props are never
asserted. -/

section GSC

open SM.Carrier SM.Link

/-! ### GSC §4 (12)–(13): the Laurent-polynomial coefficient extraction (pure algebra, PROVED) -/

/-- Floors multiply: if every monomial of `f` has exponent `≥ dA` and every monomial of `g` has
exponent `≥ dB`, the `a^{dA+dB}` coefficient of `f * g` is the product of the two floor
coefficients ("the coefficient at `D = d_A + d_B` is the product of the two first coefficients"). -/
theorem gsc_coeff_mul_floor {f g : LaurentPolynomial ℤ} {dA dB : ℤ}
    (hf : ∀ i, f.coeff i ≠ 0 → dA ≤ i) (hg : ∀ j, g.coeff j ≠ 0 → dB ≤ j) :
    (f * g).coeff (dA + dB) = f.coeff dA * g.coeff dB := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  rw [Finset.sum_eq_single dA, Finset.sum_eq_single dB, ite_eq_left rfl]
  · intro j hj hne
    rw [ite_eq_right]
    intro he
    have := hg j (Finsupp.mem_support_iff.mp hj)
    omega
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, mul_zero, ite_eq_left rfl]
  · intro i hi hne
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [ite_eq_right]
    intro he
    have h1 := hf i (Finsupp.mem_support_iff.mp hi)
    have h2 := hg j (Finsupp.mem_support_iff.mp hj)
    omega
  · intro h
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.notMem_support_iff.mp h, zero_mul, ite_self]

/-- Below the sum of the floors every coefficient of the product vanishes ("no exponent below `d_A`
occurs in `f_A`, and none below `d_B` occurs in `f_B`. Therefore the first coefficient in (12) is
zero"). -/
theorem gsc_coeff_mul_eq_zero_of_lt {f g : LaurentPolynomial ℤ} {dA dB : ℤ}
    (hf : ∀ i, f.coeff i ≠ 0 → dA ≤ i) (hg : ∀ j, g.coeff j ≠ 0 → dB ≤ j) {k : ℤ}
    (hk : k < dA + dB) : (f * g).coeff k = 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  rw [ite_eq_right]
  intro he
  have h1 := hf i (Finsupp.mem_support_iff.mp hi)
  have h2 := hg j (Finsupp.mem_support_iff.mp hj)
  omega

/-- The `a^k` coefficient of `(a − a⁻¹) a^{−2ℓ} h` is `[a^{k+2ℓ−1}] h − [a^{k+2ℓ+1}] h` ("the factor
`a^(-2 ell)(a-a^(-1))`"). -/
theorem gsc_coeff_shift (ℓ k : ℤ) (h : LaurentPolynomial ℤ) :
    ((aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * h).coeff k =
      h.coeff (k + 2 * ℓ - 1) - h.coeff (k + 2 * ℓ + 1) := by
  have e1 : (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) =
      (LaurentPolynomial.T (1 + -(2 * ℓ)) : LaurentPolynomial ℤ) -
        LaurentPolynomial.T (-1 + -(2 * ℓ)) := by
    rw [LaurentPolynomial.T_add, LaurentPolynomial.T_add, sub_mul]
  rw [e1, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, LaurentPolynomial.T,
    LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul, one_mul]
  congr 2 <;> ring

/-- **GSC (12)–(13), the coefficient extraction.**  From lem:fulltwist's coefficient display, the
two-component `z^{-1}` row of lem:homflyrows (ii) (already in product-of-rows form, knot parity
included), the slot identity (11) `d_A + d_B = d_L + 2ℓ` and the two floors of thm:carrierfloor,
`Ω_H − Ω_L = −ω_A ω_B`. -/
theorem gsc_omega_jump_alg {ΩH ΩL dL dA dB ℓ : ℤ} {F0 QA QB : R}
    (hfull : ΩH - ΩL = coeffAt (dL - 1) (-1) F0)
    (hrow : zRow (-1) F0 = (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * (zRow 0 QA * zRow 0 QB))
    (hD : dA + dB = dL + 2 * ℓ)
    (hA : ∀ d, coeffAt d 0 QA ≠ 0 → dA ≤ d) (hB : ∀ d, coeffAt d 0 QB ≠ 0 → dB ≤ d) :
    ΩH - ΩL = -(coeffAt dA 0 QA * coeffAt dB 0 QB) := by
  have hA' : ∀ i, (zRow 0 QA).coeff i ≠ 0 → dA ≤ i := fun i hi => hA i (by rwa [coeff_zRow] at hi)
  have hB' : ∀ j, (zRow 0 QB).coeff j ≠ 0 → dB ≤ j := fun j hj => hB j (by rwa [coeff_zRow] at hj)
  rw [hfull, ← coeff_zRow, hrow, gsc_coeff_shift]
  have e2 : dL - 1 + 2 * ℓ + 1 = dA + dB := by omega
  rw [e2, gsc_coeff_mul_floor hA' hB',
    gsc_coeff_mul_eq_zero_of_lt hA' hB' (k := dL - 1 + 2 * ℓ - 1) (by omega), coeff_zRow, coeff_zRow]
  ring

/-! ### The def:X1 objects of a carrier as lem:fulltwist's `d`, `Ω` of its grouped diagram
(cor:groupedknot (B): `D_L`, `D_H` are the positive lifts `carrierDiagram`) -/

variable {P P' : LabelledTuple n}

/-- A grouped carrier diagram is carried by a single closed plane curve (cor:groupedknot (B)). -/
theorem gsc_carrierDiagram_componentCount (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierDiagram hn hG hS q).componentCount = 1 :=
  ((CV.groupedknot hn hG hS q).retain_all).1

/-- `w(D(W)) = w_{S,L}` for every carrier (cor:groupedknot (B) `grouped_writhe`; `0 = 0` when
piece-free). -/
theorem gsc_carrierDiagram_writhe (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierDiagram hn hG hS q).writhe = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS q]
  exact geoPositiveLift_writhe hn _ _ q

/-- `R(Γ_{D(W)}) = R(L)`: the underlying curve of the grouped diagram is the carrier's corner polygon
(cor:groupedknot (B) `underlying_curve`, definitional). -/
theorem gsc_carrierDiagram_absRot (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (h1 : (CV.carrierDiagram hn hG hS q).componentCount = 1) :
    CV.absRot (CV.carrierDiagram hn hG hS q) h1 = (CV.carrierR hn hG hS q : ℤ) := rfl

/-- lem:fulltwist's `d(D(W)) = 1 − w − R` is def:X1's slot of the carrier. -/
theorem gsc_d_carrierDiagram (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (h1 : (CV.carrierDiagram hn hG hS q).componentCount = 1) :
    CV.d (CV.carrierDiagram hn hG hS q) h1 = CV.slot hn hG hS q := by
  unfold CV.d CV.slot
  rw [gsc_carrierDiagram_writhe, gsc_carrierDiagram_absRot]

/-- lem:fulltwist's `Ω(D(W))` is def:X1's factor `Ω₁(S,L)` ("The two bindings agree wherever both
apply"). -/
theorem gsc_Omega_carrierDiagram (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (h1 : (CV.carrierDiagram hn hG hS q).componentCount = 1) :
    CV.Omega (CV.carrierDiagram hn hG hS q) h1 = CV.Omega1 hn hG hS q := by
  unfold CV.Omega CV.Omega1
  rw [gsc_d_carrierDiagram, GT_groupedPoly_eq_homfly]

/-! ### A uniform carrier satisfies the alternative of thm:carrierfloor (C)/(D) -/

/-- "The nonzero-selector assumption and (4) make each such carrier uniform with turn sign `−σ`; after
a possible global orientation reversal, thm:carrierfloor (C) applies": a uniform carrier (def:wind) is
all-positive or, after reversal, all-positive (`UniformOrOneDissentCV` of its corner polygon). -/
theorem gsc_alt_of_uniform (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hu : CV.CarrierUniform hG.crossingGeometry S q) :
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q) := by
  obtain ⟨τ, hτ, hk⟩ := hu
  have hsm : SM.Regular (geoCornerPolygon hG.crossingGeometry S q) :=
    (CV.regular_iff_sm _).mp (CV.carrierPolygon_cvRegular hn hG hS q)
  cases τ with
  | zero => exact absurd rfl hτ
  | pos =>
    left; left
    intro i
    have h : SignType.sign (det (edge (geoCornerPolygon hG.crossingGeometry S q) (i - 1))
        (edge (geoCornerPolygon hG.crossingGeometry S q) i)) = 1 := by
      rw [← turn_det]; exact hk i
    exact (CV.principalAngle_pos_iff (hsm i)).mpr (sign_eq_one_iff.mp h)
  | neg =>
    right; left
    intro i
    have h : SignType.sign (det (edge (geoCornerPolygon hG.crossingGeometry S q) (2 - i - 1))
        (edge (geoCornerPolygon hG.crossingGeometry S q) (2 - i))) = -1 := by
      rw [← turn_det]; exact hk (2 - i)
    have hneg : SM.principalTurn (geoCornerPolygon hG.crossingGeometry S q) (2 - i) < 0 :=
      (principalAngle_neg_iff _ _).mpr (sign_eq_neg_one_iff.mp h)
    rw [CV.principalTurn_eq_sm, principalTurn_reversal hsm i]
    linarith

/-- The floor of thm:carrierfloor (C)/(D) in support form, at a carrier of nonzero weight. -/
theorem gsc_floor_of_weight_ne_zero (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hw : CV.weight hG.crossingGeometry S q ≠ 0) (d : ℤ)
    (hd : coeffAt d 0 (CV.groupedPoly hn hG hS q) ≠ 0) : CV.slot hn hG hS q ≤ d :=
  hF.coeff_zero hn hG hS q
    (gsc_alt_of_uniform hn hG hS q ((CV.weight_ne_zero_iff hG.crossingGeometry S q).mp hw)) d hd

/-! ### The interface Props (D-F11): the G10 move and the diagram identifications of GSC §3 -/

/-- **Interface (G10): the full-twist triple of GSC §3.**  "In (3), choose the positive crossing `a` and
let `D_0` be its oriented smoothing.  Switching `a` makes `a, c` an empty oppositely signed oriented RII
pair; deleting that pair gives `D_L`.  Thus `(D_L, D_H, D_0)` satisfies (T1)–(T2) of lem:fulltwist":
`q` (the retained crossing `a` of `D_H`) is positive, `D₀` is an oriented smoothing of `D_H` at `q`
(T1), and the switched diagram is carried by RII moves (T2) to a diagram `D_L'` with the polynomial of
`D_L` — the RII deletion of the switched empty pair is the one move of this unit.  `D_L` is the grouped
diagram of the `P-b` carrier, which lives on the OTHER side of the wall, so the RII deletion (performed
on the `E`-side lift `D_H`) lands on a diagram with the RECORD of `D_L` (lem:carrierword, def:record),
whose polynomial is `P_{D_L}` by ax:gausscode (`CV.gausscode_polynomial`); the printed (T2) "gives a
diagram carried to `D_L`" is read through that identification (`homfly D_L' = homfly D_L`), which is all
lem:fulltwist's first display consumes (`CV.fulltwist_skein` at `D_L'`). -/
def gsc_fulltwist_triple (D_L D_H D₀ : Diagram) (q : D_H.Γ.Crossing) : Prop :=
  D_H.IsPositive q ∧ IsOrientedSmoothing D_H q D₀ ∧
    ∃ D_L' : Diagram, Relation.ReflTransGen RII (D_H.switch q) D_L' ∧ homfly D_L' = homfly D_L

/-- **Interface: the smoothing identification of GSC §3.**  "Smoothing `a` in (3) gives two ordered
components.  The first inherits the `A` successor string and the second the `B` string … After deleting
those mixed crossings from the component records, the retained visits, cyclic order, over/under
designations, and positive crossing signs are exactly the records on the `P-ac` `A` and `B` carriers
… By lem:carrierword, def:record, ax:gausscode, and cor:groupedknot, the two component polynomials are
the pair-row grouped polynomials `Q_A, Q_B`": `D₀` has two components `i ≠ j`, whose knot restrictions
have the grouped polynomials `QA`, `QB` (ax:gausscode on the record isomorphisms), and `ℓ` is their
linking number (lem:homflyrows (ii)'s `2λ = mixedSignSum`). -/
def gsc_smoothing_split (D₀ : Diagram) (i j : Fin D₀.Γ.c) (QA QB : R) (ℓ : ℤ) : Prop :=
  D₀.componentCount = 2 ∧ i ≠ j ∧ homfly (D₀.knotRestrict i) = QA ∧ homfly (D₀.knotRestrict j) = QB ∧
    CV.IsLinkingNumber D₀ i j ℓ

/-- **The ledger data of the generic selected couple on an abstract configuration** (GSC §1–§3):
two CV-generic polygons `P` (the two-edge side, local words `P = a b A a c B b c C`) and `P'` (the
one-edge side, `E = b a A c a B c b C`) with the same crossing set, an outside support `Q`, the centre
`m` (= `b`) and the selected pair `x, w` (= `a, c`); the rows `S_m = Q ∪ {m}` (present on both sides)
and `S_xw = Q ∪ {x, w}` (present on `P`).  Fields, by GSC section:
* §1 (2) the successor carriers: `qC`, `qAB` on `P-b`; `qC'`, `qA`, `qB` on `P-ac`; the wall bijection
  `τ` of the centre row (rows 164/173: `GT_Wall`, `GT_carrierEquiv`) and the bijection `ρ` of the
  carriers of `P-b` onto those of `P-ac` other than `B` (`AB ↦ A`, `C ↦ C'`, every other carrier "identical");
* §2 (4)–(7) the selector and rotation ledger: `weight_wall`, `carrierR_wall` (the `P-b`/`E-b` carriers
  "form a path in `R_c` through the RIII family"), `weight_C` (`wt(C_ac) = −σ wt(C_b)`), `weight_AB`
  (`wt(A) wt(B) = σ wt(AB)`), `carrierR_add` ((8) `R(A)+R(B) = R(AB)` under a nonzero selector),
  `spectator_*` and `omega_wall`/`omega_C` (the common spectator reads and `Ω_C`);
* §3 the grouped full-twist triple: `writhe_wall` ((9) `w_H = w_L + 2`), `fulltwist` (the G10 RII
  deletion), `smoothing` (the two-component smoothing carries the `P-ac` records), `writhe_count`
  ((10) `w_L = w_A + w_B + 2ℓ − 1`).
`σ = ±1` is the canonical sign (1). -/
structure gsc_WallData (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (Q : Finset (Crossing P)) (m : Crossing P)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry) where
  /-- (2) `E-b : C | AB`: the carriers of the centre row correspond across the wall. -/
  τ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
  /-- (6) the local corner signs of `P-b` and `E-b` agree carrier by carrier. -/
  weight_wall : ∀ q, CV.weight hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (τ q) =
    CV.weight hG.crossingGeometry (Q ∪ {m}) q
  /-- (7) `rot(C_b) = rot(C_E)`, `rot(AB) = rot(AB_E)`. -/
  carrierR_wall : ∀ q, CV.carrierR hn hG' hSm' (τ q) = CV.carrierR hn hG hSm q

/-! ### REALISED: the wall part of the ledger (GSC §1 (2), §2 (6)–(7) for the `P-b`/`E-b` carriers),
from the accepted row-173 toolkit (`GT_Wall`, `GT_carrierEquiv`, `GT_weight_eq`, `GT_carrierR_eq`) on
a `GT_Endpoint` configuration -/

/-- The wall data of the centre row `Q ∪ {m}`: as `GT_Endpoint.wall` for the row `Q ∪ {x}`, with the
one selected triangle crossing now the centre `m` (`corners_apart`: two corners of `Q ∪ {m}` that are
both triangle crossings are both `m`). -/
theorem gsc_wall_of_endpoint (hG : CV.Generic P) (hG' : CV.Generic P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
    {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry) :
    GT_Wall hG.crossingGeometry hG'.crossingGeometry hs (triangleCrossings P e f g) (Q ∪ {m}) where
  indep := CV.geoIndependent_of_mem_Ind _ hSm
  indep' := CV.geoIndependent_of_mem_Ind _ hSm'
  key_lt v w hvw := AV_key_lt_of_gauss _ _ hs D.hef D.heg D.hfg D.gauss v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvS, hwS⟩
    have key : ∀ y : Crossing P, y ∈ Q ∪ {m} → y.val ∈ triangleSupports e f g → y = m := by
      intro y hy hyT
      rcases Finset.mem_union.mp hy with hyQ | hym
      · exact absurd hyT (D.Q_out y hyQ)
      · exact Finset.mem_singleton.mp hym
    have h1 := key v.1 hvS ((F1.mem_triangleCrossings e f g v.1).mp hrev.1)
    have h2 := key w.1 hwS ((F1.mem_triangleCrossings e f g w.1).mp hrev.2.1)
    exact hrev.2.2.1 (h1.trans h2.symm)
  turn_eq := D.turn_eq
  sign_eq := D.sign_eq
  ray := D.ray

/-- **The wall part of the ledger is realised**: `τ` is the corner-cycle correspondence
`GT_carrierEquiv`, the selectors and rotations are carried (`GT_weight_eq`, `GT_carrierR_eq`). -/
noncomputable def gsc_wallData_of_endpoint (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
    {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry) :
    gsc_WallData hn hG hG' hs Q m hSm hSm' where
  τ := GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm')
  weight_wall := GT_weight_eq hn hG hG' (gsc_wall_of_endpoint hG hG' D hSm hSm')
  carrierR_wall := GT_carrierR_eq hn hG hG' (gsc_wall_of_endpoint hG hG' D hSm hSm') hSm hSm'


/-- **The canonical sign is realised**: `σ = sgn det(u₁,u₂)` is `±1` on a CV-generic polygon at an
actual crossing (genericity (G5), `CV.Generic.g5` through `crosses_iff`). -/
theorem gsc_sigma_of_generic (hG : CV.Generic P) {i j : ZMod n} (h : IsCrossing P {i, j}) :
    ((crossingSign P i j : SignType) : ℤ) = 1 ∨ ((crossingSign P i j : SignType) : ℤ) = -1 := by
  have hne : crossingSign P i j ≠ 0 := by
    rw [← strandSign_eq_crossingSign]
    exact sign_ne_zero.mpr (hG.g5 ((hG.crosses_iff i j).mpr h))
  cases hc : crossingSign P i j with
  | zero => exact absurd hc hne
  | pos => left; rfl
  | neg => right; rfl

/-- On a `GT_Endpoint` configuration the sign `crossingSign ℓ₁ ℓ₂` is `±1`. -/
theorem gsc_sigma_of_endpoint (hG : CV.Generic P) {hP' : CrossingGeometry P'}
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
    {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (D : GT_Endpoint hG.crossingGeometry hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) :
    ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ) = 1 ∨ ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ) = -1 :=
  gsc_sigma_of_generic hG (GT_isCrossing_of_mem D.x1 D.x2 D.l12)

/-- The ledger data proper, over the REALISED wall data `W` (`gsc_wallData_of_endpoint`): these
fields are the interface. -/
structure gsc_Ledger (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (Q : Finset (Crossing P)) (m x w : Crossing P)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (W : gsc_WallData hn hG hG' hs Q m hSm hSm') where
  /-- (1) the canonical sign `σ`. -/
  σ : ℤ
  hσ : σ = 1 ∨ σ = -1
  /-- (2) `P-b : C | AB`. -/
  qC : GeoComponent hG.crossingGeometry (Q ∪ {m})
  qAB : GeoComponent hG.crossingGeometry (Q ∪ {m})
  hCAB : qC ≠ qAB
  /-- (2) `P-ac : C | A | B`. -/
  qC' : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  qA : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w})
  hC'A : qC' ≠ qA
  hC'B : qC' ≠ qB
  hAB : qA ≠ qB
  /-- "The `C` carrier in (2) owns the same residual labels in all three rows … Every other carrier is
  a common spectator with the same data": every carrier but `AB` has the same read across the wall. -/
  omega_wall : ∀ q, q ≠ qAB → CV.Omega1 hn hG' hSm' (W.τ q) = CV.Omega1 hn hG hSm q
  /-- (9) "`D_H` has exactly the two additional positive residual crossings `a, c`": `w_H = w_L + 2`. -/
  writhe_wall : CV.groupedWrithe hG' (W.τ qAB) = CV.groupedWrithe hG qAB + 2
  /-- (2) the carriers of `P-b` against those of `P-ac`: `AB ↦ A`, `C ↦ C'`, spectators to themselves;
  `B` is the extra carrier of the pair row. -/
  ρ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    {q' : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) // q' ≠ qB}
  ρ_AB : (ρ qAB).1 = qA
  ρ_C : (ρ qC).1 = qC'
  spectator_weight : ∀ q, q ≠ qAB → q ≠ qC →
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) (ρ q).1 = CV.weight hG.crossingGeometry (Q ∪ {m}) q
  spectator_omega : ∀ q, q ≠ qAB → q ≠ qC → CV.Omega1 hn hG hSxw (ρ q).1 = CV.Omega1 hn hG hSm q
  /-- "its retained signed cyclic record, grouped writhe, rotation, slot, and read are the same". -/
  omega_C : CV.Omega1 hn hG hSxw qC' = CV.Omega1 hn hG hSm qC
  /-- (5) `wt(C_ac) = −σ wt(C_b)`. -/
  weight_C : CV.weight hG.crossingGeometry (Q ∪ {x, w}) qC' = -σ * CV.weight hG.crossingGeometry (Q ∪ {m}) qC
  /-- (5) `wt(A) wt(B) = σ wt(AB)` ("including the mixed cases"). -/
  weight_AB : CV.weight hG.crossingGeometry (Q ∪ {x, w}) qA * CV.weight hG.crossingGeometry (Q ∪ {x, w}) qB =
    σ * CV.weight hG.crossingGeometry (Q ∪ {m}) qAB
  /-- (7)–(8) `R(A) + R(B) = R(AB)` when the selector is nonzero (turnlift (ii) + uniformrot (i)). -/
  carrierR_add : CV.weight hG.crossingGeometry (Q ∪ {m}) qAB ≠ 0 →
    CV.carrierR hn hG hSm qAB = CV.carrierR hn hG hSxw qA + CV.carrierR hn hG hSxw qB
  /-- §3 the oriented smoothing `D_0` of `D_H` at `a`. -/
  D₀ : Diagram
  /-- the positive crossing `a` of `D_H`. -/
  qx : (CV.carrierDiagram hn hG' hSm' (W.τ qAB)).Γ.Crossing
  /-- (T1)–(T2): the G10 RII deletion (interface `gsc_fulltwist_triple`). -/
  fulltwist : gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' (W.τ qAB)) D₀ qx
  /-- the two ordered components of `D_0`. -/
  i : Fin D₀.Γ.c
  j : Fin D₀.Γ.c
  /-- the linking number `ℓ`. -/
  ℓ : ℤ
  /-- the smoothing identification (interface `gsc_smoothing_split`). -/
  smoothing : gsc_smoothing_split D₀ i j (CV.groupedPoly hn hG hSxw qA) (CV.groupedPoly hn hG hSxw qB) ℓ
  /-- (10) `w_L = w_A + w_B + 2ℓ − 1`. -/
  writhe_count : CV.groupedWrithe hG qAB = CV.groupedWrithe hG qA + CV.groupedWrithe hG qB + 2 * ℓ - 1

/-! ### The RA ledger on an abstract configuration (GSC §4–§5), PROVED from the interface -/

/-- A present row is the product over its carriers of `wt(L) Ω₁(S,L)` (def:wind + def:X1). -/
theorem gsc_rowTerm_eq_prod (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) :
    rowTerm hn hG S = ∏ q : GeoComponent hG.crossingGeometry S,
      CV.weight hG.crossingGeometry S q * CV.Omega1 hn hG hS q := by
  rw [rowTerm_of_mem_Ind hn hG hS]
  unfold CV.wind
  rw [Finset.prod_mul_distrib]

/-- Splitting two distinguished factors off a product over a `Fintype`. -/
theorem gsc_prod_split {α : Type*} [Fintype α] [DecidableEq α] (F : α → ℤ) (a b : α) (hab : a ≠ b) :
    ∏ q, F q = F a * (F b * ∏ q ∈ (Finset.univ.erase a).erase b, F q) := by
  rw [Finset.mul_prod_erase (Finset.univ.erase a) F
    (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  rw [Finset.mul_prod_erase Finset.univ F (Finset.mem_univ a)]

/-- **GSC (13) on the ledger: `Ω_H − Ω_L = −ω_A ω_B`** under a nonzero selector.  lem:fulltwist's
coefficient display at the triple `(D_L, D_H, D_0)` with `d_H = d_L − 2` from (9) and (7); lem:homflyrows
(ii) with knot parity on the two components; (10)+(8) give (11); the two floors from
`CV.CarrierSlotFloor` at the uniform carriers `A`, `B` (their weights are nonzero by (5)). -/
theorem gsc_omega_jump (hF : CV.CarrierSlotFloor) {hn : 3 ≤ n} {hG : CV.Generic P} {hG' : CV.Generic P'}
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {Q : Finset (Crossing P)} {m x w : Crossing P}
    {hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry} {hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry}
    {hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry}
    {W : gsc_WallData hn hG hG' hs Q m hSm hSm'} (L : gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' W)
    (h0 : CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB ≠ 0) :
    CV.Omega1 hn hG' hSm' (W.τ L.qAB) - CV.Omega1 hn hG hSm L.qAB =
      -(CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB) := by
  -- the selectors of `A` and `B` are nonzero (5)
  have hσ0 : L.σ ≠ 0 := by rcases L.hσ with h | h <;> rw [h] <;> decide
  have hprod : CV.weight hG.crossingGeometry (Q ∪ {x, w}) L.qA *
      CV.weight hG.crossingGeometry (Q ∪ {x, w}) L.qB ≠ 0 := by
    rw [L.weight_AB]; exact mul_ne_zero hσ0 h0
  have hA0 := left_ne_zero_of_mul hprod
  have hB0 := right_ne_zero_of_mul hprod
  -- the floors
  have hFA := gsc_floor_of_weight_ne_zero hF hn hG hSxw L.qA hA0
  have hFB := gsc_floor_of_weight_ne_zero hF hn hG hSxw L.qB hB0
  -- lem:fulltwist's first display at the grouped triple, the switched diagram read through the
  -- record identification `homfly D_L' = homfly D_L`
  obtain ⟨hpos, T1, D_L', T2, hLL'⟩ := L.fulltwist
  have hsk := CV.fulltwist_skein D_L' _ L.D₀ L.qx hpos T1 T2
  rw [hLL', ← GT_groupedPoly_eq_homfly, ← GT_groupedPoly_eq_homfly] at hsk
  -- (9): `d_H = d_L − 2`
  have hd : CV.slot hn hG' hSm' (W.τ L.qAB) = CV.slot hn hG hSm L.qAB - 2 := by
    unfold CV.slot
    rw [L.writhe_wall, W.carrierR_wall]
    ring
  -- lem:fulltwist's second display, as printed (d6:2039–2044): `Ω_H = [a^{d_L−2} z^0] F_H`, the first
  -- term contributes `[a^{d_L} z^0] F_L = Ω_L`, the second `[a^{d_L−1} z^{−1}] F_A`
  have hfull : CV.Omega1 hn hG' hSm' (W.τ L.qAB) - CV.Omega1 hn hG hSm L.qAB =
      coeffAt (CV.slot hn hG hSm L.qAB - 1) (-1) (homfly L.D₀) := by
    unfold CV.Omega1
    rw [hd, hsk, coeffAt_add, CV.R.aInv_sq, CV.R.aInv_mul_z, CV.coeffAt_single_mul,
      CV.coeffAt_single_mul]
    have e1 : CV.slot hn hG hSm L.qAB - 2 - -2 = CV.slot hn hG hSm L.qAB := by ring
    have e2 : CV.slot hn hG hSm L.qAB - 2 - -1 = CV.slot hn hG hSm L.qAB - 1 := by ring
    rw [e1, e2]
    norm_num
  -- lem:homflyrows (ii) with knot parity
  obtain ⟨h2, hij, hQA, hQB, hlink⟩ := L.smoothing
  have hrow := CV.two_component_row_rows L.D₀ L.i L.j h2 hij L.ℓ hlink
  rw [hQA, hQB] at hrow
  -- (11) from (10) and (8)
  have hD : CV.slot hn hG hSxw L.qA + CV.slot hn hG hSxw L.qB = CV.slot hn hG hSm L.qAB + 2 * L.ℓ := by
    unfold CV.slot
    rw [L.writhe_count, L.carrierR_add h0]
    push_cast
    ring
  exact gsc_omega_jump_alg hfull hrow hD hFA hFB

/-- **The generic selected complementary couple on an abstract configuration** (GSC §5):
`T_E(b) − T_P(b) = wind_P(Q ∪ b) V Ω_C (Ω_H − Ω_L) = −wind_P(Q ∪ b) V Ω_C ω_A ω_B = T_P(ac)`, "including
the mixed cases rather than cancelling a possibly zero weight … no exterior factor was divided out". -/
theorem gsc_couple_of_ledger (hF : CV.CarrierSlotFloor) {hn : 3 ≤ n} {hG : CV.Generic P}
    {hG' : CV.Generic P'} {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {Q : Finset (Crossing P)}
    {m x w : Crossing P} {hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry}
    {hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry}
    {hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry}
    {W : gsc_WallData hn hG hG' hs Q m hSm hSm'} (L : gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' W) :
    rowTerm hn hG' (transportSupport hs (Q ∪ {m})) =
      rowTerm hn hG (Q ∪ {m}) + rowTerm hn hG (Q ∪ {x, w}) := by
  classical
  -- the three rows as products of `wt · Ω₁`
  set F : GeoComponent hG.crossingGeometry (Q ∪ {m}) → ℤ :=
    fun q => CV.weight hG.crossingGeometry (Q ∪ {m}) q * CV.Omega1 hn hG hSm q with hF_def
  set F' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) → ℤ :=
    fun q => CV.weight hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q *
      CV.Omega1 hn hG' hSm' q with hF'_def
  set G : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) → ℤ :=
    fun q => CV.weight hG.crossingGeometry (Q ∪ {x, w}) q * CV.Omega1 hn hG hSxw q with hG_def
  have e1 : rowTerm hn hG (Q ∪ {m}) = ∏ q, F q := gsc_rowTerm_eq_prod hn hG hSm
  have e2 : rowTerm hn hG' (transportSupport hs (Q ∪ {m})) = ∏ q, F' q := gsc_rowTerm_eq_prod hn hG' hSm'
  have e3 : rowTerm hn hG (Q ∪ {x, w}) = ∏ q, G q := gsc_rowTerm_eq_prod hn hG hSxw
  -- the common spectator product `V`
  set V : ℤ := ∏ q ∈ (Finset.univ.erase L.qAB).erase L.qC, F q with hV
  -- (i) the centre row on `P`
  have h1 : ∏ q, F q = F L.qAB * (F L.qC * V) := gsc_prod_split F L.qAB L.qC L.hCAB.symm
  -- (ii) the centre row on `P'`, reindexed along `τ`
  have h2 : ∏ q, F' q = (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
      CV.Omega1 hn hG' hSm' (W.τ L.qAB)) * (F L.qC * V) := by
    rw [← Fintype.prod_equiv W.τ (fun q => F' (W.τ q)) F' (fun _ => rfl),
      gsc_prod_split (fun q => F' (W.τ q)) L.qAB L.qC L.hCAB.symm]
    have hC : F' (W.τ L.qC) = F L.qC := by
      simp only [hF'_def, hF_def]
      rw [W.weight_wall, L.omega_wall L.qC L.hCAB]
    have hAB : F' (W.τ L.qAB) = CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
        CV.Omega1 hn hG' hSm' (W.τ L.qAB) := by
      simp only [hF'_def]
      rw [W.weight_wall]
    have hV' : ∏ q ∈ (Finset.univ.erase L.qAB).erase L.qC, F' (W.τ q) = V := by
      refine Finset.prod_congr rfl fun q hq => ?_
      have hqAB : q ≠ L.qAB := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
      simp only [hF'_def, hF_def]
      rw [W.weight_wall, L.omega_wall q hqAB]
    rw [hC, hAB, hV']
  -- (iii) the pair row on `P`, `B` split off and the rest reindexed along `ρ`
  have h3' : ∏ q' ∈ Finset.univ.erase L.qB, G q' = ∏ q, G (L.ρ q).1 := by
    symm
    refine Finset.prod_bij' (fun q _ => (L.ρ q).1)
      (fun q' hq' => L.ρ.symm ⟨q', (Finset.mem_erase.mp hq').1⟩)
      (fun q _ => Finset.mem_erase.mpr ⟨(L.ρ q).2, Finset.mem_univ _⟩) (fun _ _ => Finset.mem_univ _)
      (fun q _ => ?_) (fun q' hq' => ?_) (fun q _ => rfl)
    · rw [Subtype.coe_eta, Equiv.symm_apply_apply]
    · rw [Equiv.apply_symm_apply]
  have hV3 : ∏ q ∈ (Finset.univ.erase L.qAB).erase L.qC, G (L.ρ q).1 = V := by
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqC : q ≠ L.qC := (Finset.mem_erase.mp hq).1
    have hqAB : q ≠ L.qAB := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    simp only [hG_def, hF_def]
    rw [L.spectator_weight q hqAB hqC, L.spectator_omega q hqAB hqC]
  have h3 : ∏ q, G q = G L.qB * (G L.qA * (G L.qC' * V)) := by
    rw [← Finset.mul_prod_erase Finset.univ G (Finset.mem_univ L.qB), h3',
      gsc_prod_split (fun q => G (L.ρ q).1) L.qAB L.qC L.hCAB.symm, L.ρ_AB, L.ρ_C, hV3]
  -- the key identity (13), with the selector kept as a factor (the zero-selector case is trivial)
  have hkey : CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
      (CV.Omega1 hn hG' hSm' (W.τ L.qAB) - CV.Omega1 hn hG hSm L.qAB) =
      -(CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB *
        (CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB)) := by
    by_cases h0 : CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB = 0
    · rw [h0]; ring
    · rw [gsc_omega_jump hF L h0]; ring
  have hσ2 : L.σ * L.σ = 1 := by rcases L.hσ with h | h <;> rw [h] <;> norm_num
  rw [e1, e2, e3, h1, h2, h3]
  simp only [hF_def, hG_def]
  rw [L.weight_C, L.omega_C]
  linear_combination
    (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qC * CV.Omega1 hn hG hSm L.qC * V) * hkey +
    (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qC * CV.Omega1 hn hG hSm L.qC * V *
      CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB * L.σ) * L.weight_AB +
    (CV.weight hG.crossingGeometry (Q ∪ {m}) L.qC * CV.Omega1 hn hG hSm L.qC * V *
      CV.Omega1 hn hG hSxw L.qA * CV.Omega1 hn hG hSxw L.qB *
      CV.weight hG.crossingGeometry (Q ∪ {m}) L.qAB) * hσ2

end GSC

/-! ### The event-level interface and the row from it -/

/-- **Interface (G10 + the identifications of GSC §1–§3), event level.**  On every two-edge-side
configuration of the generic orbit at full availability (`GT_Endpoint`: `x, w` the selected pair, `m`
the centre, `ℓ₁` shared by `x, m`, `ℓ₂` by `x, w`, `ℓ₃` by `w, m`; R-LOC (2)–(4), lem:guardconst, the
masks) in the canonical sign branch (1) (`crossingSign ℓ₁ ℓ₂ = crossingSign ℓ₁ ℓ₃`, together with
`GT_Endpoint.sgn`: all three strand-determinant signs equal `σ`), the ledger data of `gsc_Ledger` exist
over the REALISED wall data `gsc_wallData_of_endpoint` (the corner-cycle correspondence `τ` with its
selector and rotation transport).  NEVER mapped: this is the obligation the realisation of the unit
discharges (report U_R174_REPORT.md). -/
def gsc_moves : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n) (Q : Finset (Crossing P))
    (x w m : Crossing P) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃),
    crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃ →
    ∀ (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
      (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry),
      Nonempty (gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' (gsc_wallData_of_endpoint hn hG hG' D hSm hSm'))

section GSCEvent

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- The centre row `Q ∪ {m}` is present on the two-edge side (full availability). -/
theorem gsc_Ind_centre {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {m : Crossing (E.curve t)} (hm : m.val ∈ triangleSupports e f g) :
    Q ∪ {m} ∈ CV.Ind (geomAt E t ht.1) :=
  PRE_union_mem_Ind_of_fullAvail hQ hfull
    (Finset.singleton_subset_iff.mpr ((F1.mem_triangleCrossings e f g m).mpr hm))
    (PRE_mem_Ind_of_card_le_one _ (by simp))

/-- The pair row `Q ∪ {x, w}` of a nonadjacent pair is present on the two-edge side. -/
theorem gsc_Ind_pair {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {x w : Crossing (E.curve t)} (hx : x.val ∈ triangleSupports e f g)
    (hw : w.val ∈ triangleSupports e f g) (hxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) :
    Q ∪ {x, w} ∈ CV.Ind (geomAt E t ht.1) := by
  refine PRE_union_mem_Ind_of_fullAvail hQ hfull ?_ ?_
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact (F1.mem_triangleCrossings e f g _).mpr hx
    · exact (F1.mem_triangleCrossings e f g _).mpr hw
  · rw [CV.mem_Ind_iff]
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxw
    · exact fun h => hxw (geometricInterlaces_symm _ h)
    · exact absurd rfl hab

/-- The centre row is present on the one-edge side too (the transported `Q` is an outside support at
full availability, rows 164/173). -/
theorem gsc_Ind_centre' (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {m : Crossing (E.curve t)} (hm : m.val ∈ triangleSupports e f g) :
    transportSupport hs (Q ∪ {m}) ∈ CV.Ind (geomAt E t' ht'.1) := by
  rw [GT_transportSupport_S]
  exact gsc_Ind_centre ht' (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) (m := crossingTransport hs m) hm

/-- **The couple on an event configuration**, from the interface: the two-edge side `t` carries the
path with centre `m`, `Q` is an outside support at full availability, the sign branch is canonical. -/
theorem gsc_couple_event (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃)
    (hsgn' : crossingSign (E.curve t) ℓ₁ ℓ₂ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {m})) =
      rowTerm hn (genericAt E t ht.1) (Q ∪ {m}) + rowTerm hn (genericAt E t ht.1) (Q ∪ {x, w}) := by
  have D := GT_endpointData hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃ hx hw hm hxw hxm
    hwm x1 m1 x2 w2 w3 m3 l12 l13 l23 hIxw hIxm hIwm hsgn
  obtain ⟨L⟩ := hmove n hn (genericAt E t ht.1) (genericAt E t' ht'.1) hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ D hsgn'
    (gsc_Ind_centre ht hQ hfull hm) (gsc_Ind_pair ht hQ hfull hx hw hIxw)
    (gsc_Ind_centre' hL ht ht' hop hs hQ hfull hm)
  exact gsc_couple_of_ledger hF L

/-- **Field `couple_canonical`** (`x = a`, `w = c`, `m = b`; `ℓ₁ = e`, `ℓ₂ = f`, `ℓ₃ = g`). -/
theorem gsc_couple_canonical (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    EdgeAB (geomAt E t ht.1) hef' heg' → EdgeBC (geomAt E t ht.1) heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef', xPair hfg'}) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen hsab hsbc hAB hBC Q hQ hfull
  exact gsc_couple_event hmove hF hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hef') (xPair hfg') (xPair heg') e f g GT_tri_ef GT_tri_fg GT_tri_eg
    (P1.xPair_ef_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg')
    (P1.xPair_eg_ne_fg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r hef heg hfg
    (GT_not_all_edges _ hgen hAB hBC) hAB (geometricInterlaces_symm _ hBC) hsbc.symm hsab

/-- **Field `couple_relabelled`**: the branches `ab` (centre `c`; `x = a`, `w = b`, `m = c`; `ℓ₁ = f`,
`ℓ₂ = e`, `ℓ₃ = g`) and `bc` (centre `a`; `x = b`, `w = c`, `m = a`; `ℓ₁ = e`, `ℓ₂ = g`, `ℓ₃ = f`). -/
theorem gsc_couple_relabelled (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      EdgeAC (geomAt E t ht.1) hef' hfg' → EdgeBC (geomAt E t ht.1) heg' hfg' →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef', xPair heg'})) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      EdgeAB (geomAt E t ht.1) hef' heg' → EdgeAC (geomAt E t ht.1) hef' hfg' →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg', xPair hfg'})) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  obtain ⟨h1, h2, h3, -⟩ := hG.nonzero t ht
  have hna := (hG.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen
  have hz1 : strandSign (E.curve t) e f ≠ 0 := sign_ne_zero.mpr h1
  have hz2 : strandSign (E.curve t) e g ≠ 0 := sign_ne_zero.mpr h2
  have hz3 : strandSign (E.curve t) f g ≠ 0 := sign_ne_zero.mpr h3
  constructor
  · intro hsel hAC hBC
    have hsbc := GT_signs_of_selectedAB _ _ _ hz1 hz2 hz3 hna hsel
    -- `x = a`, `w = b`, `m = c`; `ℓ₁ = f`, `ℓ₂ = e`, `ℓ₃ = g`
    refine gsc_couple_event hmove hF hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
      (xPair hef') (xPair heg') (xPair hfg') f e g GT_tri_ef GT_tri_eg GT_tri_fg
      (P1.xPair_ef_ne_eg hef' heg' hfg') (P1.xPair_ef_ne_fg hef' heg' hfg')
      (P1.xPair_eg_ne_fg hef' heg' hfg')
      GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r
      hef.symm hfg heg (GT_not_all_edges' _ hgen hAC hBC) hAC hBC hsbc ?_
    -- `crossingSign f e = crossingSign f g ⟸ s_a = −s_b, s_b = s_c`
    show crossingSign (E.curve t) f e = crossingSign (E.curve t) f g
    rw [crossingSign_swap (E.curve t) e f]
    show -strandSign (E.curve t) e f = strandSign (E.curve t) f g
    rw [hsel, neg_neg, hsbc]
  · intro hsel hAB hAC
    have hsab := GT_signs_of_selectedBC _ _ _ hz1 hz2 hz3 hna hsel
    -- `x = b`, `w = c`, `m = a`; `ℓ₁ = e`, `ℓ₂ = g`, `ℓ₃ = f`
    refine gsc_couple_event hmove hF hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
      (xPair heg') (xPair hfg') (xPair hef') e g f GT_tri_eg GT_tri_fg GT_tri_ef
      (P1.xPair_eg_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg').symm
      (P1.xPair_ef_ne_fg hef' heg' hfg').symm
      GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r
      heg hef hfg.symm (GT_not_all_edges'' _ hgen hAB hAC) (geometricInterlaces_symm _ hAB)
      (geometricInterlaces_symm _ hAC) ?_ ?_
    · -- `crossingSign g f = crossingSign e f ⟸ s_a = s_b, s_b = −s_c`
      show crossingSign (E.curve t) g f = crossingSign (E.curve t) e f
      rw [crossingSign_swap (E.curve t) f g]
      show -strandSign (E.curve t) f g = strandSign (E.curve t) e f
      rw [hsab, hsel]
    · -- `crossingSign e g = crossingSign e f ⟸ s_a = s_b`
      exact hsab.symm

/-- **The bundle of row 174 from the interface** at a radius carrying rows 164, 172's table and the
event sign data. -/
theorem gsc_genericSelectedData (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : GenericSelectedData hn E e f g δ where
  couple_canonical := gsc_couple_canonical hmove hF hn hL hG hR hef heg hfg
  couple_relabelled := gsc_couple_relabelled hmove hF hn hL hG hR hef heg hfg

end GSCEvent

/-- **The RA ledger of row 174** (D-F11): from the interface `gsc_moves` and the carrier floor
`CV.CarrierSlotFloor` (thm:carrierfloor (C)+(D) in def:X1's symbols), the row in its fixed shape.  The
radius is the common one of rows 164 (`localization`), 172's table (`generic_table`) and the event sign
data (`AV_exists_eventRadius`), as for row 173. -/
theorem gsc_ledger (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) : RowShape @GenericSelectedData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact gsc_genericSelectedData hmove hF hn hL' hGT' hR' hef heg hfg


/-- The row in the exact signature of the leaf `generic_selected`, from the interface and the carrier
floor: once `gsc_moves` is realised (`hmove`), the leaf is
`gsc_generic_selected_of_moves hmove (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) hn E e f g h3 h4e h4f h4g hE`. -/
theorem gsc_generic_selected_of_moves (hmove : gsc_moves) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n)
    (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  gsc_ledger hmove hF n hn E e f g h3 h4e h4f h4g hE

/-- **Row 174, R:generic_selected** (FIXED name; R_GENERIC_SELECTED_COUPLE_PROOF.md).  Unit U-174.
Consumes: rows 168, 171, 172, 173 (`GT_Wall` transport, `G11_Config`), CV:lem:fulltwist,
CV:lem:homflyrows (ii), ax:homfly knot parity (`cvt_groupedPoly_inSupportM`), CV:lem:turnlift (ii),
CV:lem:uniformrot, cor:groupedknot (A)(B), `CV.CarrierSlotFloor` (the (C)+(D) corollary, §1.3); plus an
RII deletion of the switched empty pair (G10, to be stated as an interface Prop first, D-F11). -/
theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ := by
  sorry

/-- The owner of a residual piece (lem:carriers (iv), accepted `pieceOwner` / `mem_piecesOn_iff`). PROVED. -/
theorem cvt_exists_owner {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hP) (H : CV.Piece hP S) : ∃ q : GeoComponent hP S, H ∈ CV.piecesOn hP S q :=
  ⟨CV.pieceOwner hP hS H, (CV.mem_piecesOn_iff hP hS _ H).mpr rfl⟩

/-- LEAF (unit U-175, ~120 lines): the `pair_row_zero` field of row 175 from row 165
(R_EXTREME_PAIR_ZERO_PROOF.md, paragraphs 4-5): `rowTerm = wind * ∏ Ω₁` (`rowTerm_of_mem_Ind`); `wind = 0`
or every carrier uniform (`weight_ne_zero_iff`, `Finset.prod_ne_zero_iff`); the third crossing `z ∉ J`
(`triangleCrossings_card`) has the singleton piece `{z}` (`PRE_175_third_singleton_piece`); its owner
(`cvt_exists_owner`) is uniform; `singleton_D_i.factor_zero` kills its `Ω₁`; `Finset.prod_eq_zero`. -/
theorem cvt_pair_row_zero_of_singleton (h165 : CV.SingletonDiData) (hn : 3 ≤ n) (E : CV.Event n)
    (e f g : ZMod n) (δ : ℝ) (hPar : ParityData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      rowTerm hn (genericAt E t ht.1) (Q ∪ J) = 0 := by
  sorry

/-- **Row 175 from row 165**: the three presupposition fields are the accepted `PRE_175_*`; `δ` is
row 167's. PROVED modulo the one leaf. -/
theorem extreme_pair_zero_of_singleton (h165 : CV.SingletonDiData) : RowShape @ExtremePairZeroData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δ, hδ, hδr, hPar⟩ := parity E e f g h3 h4e h4f h4g hE
  exact ⟨δ, hδ, hδr, PRE_175_pair_absent_on_complete E e f g δ, PRE_175_pair_present_on_empty E e f g δ,
    PRE_175_third_singleton_piece hPar, cvt_pair_row_zero_of_singleton h165 hn E e f g δ hPar⟩

/-- **Row 175, R:extreme_pair_zero** (FIXED name), from row 165. -/
theorem extreme_pair_zero (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ :=
  extreme_pair_zero_of_singleton CV.singleton_D_i n hn E e f g h3 h4e h4f h4g hE

/-- **Row 176, R:extreme_transport** (FIXED name; R_EXTREME_SINGLETON_TRANSPORT_PROOF.md).  Unit U-176.
Consumes: rows 168, 171, 173 (`GT_Wall`/`GT_Relabel`), CV:selector_A, CV:lem:fulltwist,
CV:lem:homflyrows (ii), knot parity, turnlift (ii), uniformrot (i)(ii), cor:groupedknot,
`CV.CarrierSlotFloor`; an RII port relation (G10, interface Prop first). -/
theorem extreme_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ := by
  sorry

/-- **Row 177, R:extreme_selected** (FIXED name; R_EXTREME_SELECTED_COUPLE_PROOF.md).  Unit U-177.
Consumes: rows 168, 171, CV:selector_A, CV:lem:homflyrows (ii)(iii), knot parity, turnlift (ii),
uniformrot, cor:groupedknot, `CV.CarrierSlotFloor`; the matched switch + RIII through the wall
(G11's `G11_Config` toolkit) and an RII after one smoothing (G10) — both as interface Props first. -/
theorem extreme_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ := by
  sorry

/-- CV:prop:chamberinv (ii) (accepted row 147, `CV.chamberinv_ii`) in the R lane's `ChamberInvII` shape. PROVED. -/
theorem cvt_chamberInvII : ChamberInvII :=
  fun _ _ hn _ _ hP hQ h => (CV.chamberinv_ii hn hP hQ h).symm

/-- **Row 178 modulo rows 174-177**, PROVED: R_ASSEMBLY_SPEC.md (3)-(4) summed over the same outside
support set (`A2_cvRNear_of_rows`, accepted, with the accepted rows 170, 172, 173) and R6
`cv_R = cv_R_near + chamberinv(ii)` (`hyp_R_of_near_of_chamberinv`, accepted); the domain is
`E.IsSimpleRIII` (CV:def:event), "its entire printed simple/transversal forced-bundle domain". -/
theorem cv_R_of_rows (h174 : RowShape @GenericSelectedData) (h175 : RowShape @ExtremePairZeroData)
    (h176 : RowShape @ExtremeTransportData) (h177 : RowShape @ExtremeSelectedData) : CV.hyp_R :=
  hyp_R_of_near_of_chamberinv
    (A2_cvRNear_of_rows rowShape_170 rowShape_172 rowShape_173 h174 h175 h176 h177)
    cvt_chamberInvII

/-- **Row 178, R:cv_theorem** (FIXED: `RProof.cv_R : CV.hyp_R`, the R6 all-parameters form of CV:ax:R). -/
theorem cv_R : CV.hyp_R :=
  cv_R_of_rows
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_selected hn E e f g h3 h4e h4f h4g hE)
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => extreme_pair_zero hn E e f g h3 h4e h4f h4g hE)
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => extreme_transport hn E e f g h3 h4e h4f h4g hE)
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => extreme_selected hn E e f g h3 h4e h4f h4g hE)

end RProof

/-! ## 4. Row 183 Bridge:theorem — `Bridge.sm_R : SM.hyp_R` (FIXED), BRIDGE.md §3 (19)-(21) -/

namespace Bridge

/-- **Row 183, Bridge:theorem.** The displayed bridge theorem (19)-(21): the proved CV R theorem gives SM's
Hypothesis R through B1-B4 — the accepted library theorem `SM.sm_R_of_cv_R` (Bridge/SmR.lean:60) at the
proved `RProof.cv_R`; no new mathematics (FR-B-183). -/
theorem sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R

/-- The same from the four open R rows (library form). PROVED. -/
theorem sm_R_of_rows (h174 : RProof.RowShape @RProof.GenericSelectedData)
    (h175 : RProof.RowShape @RProof.ExtremePairZeroData)
    (h176 : RProof.RowShape @RProof.ExtremeTransportData)
    (h177 : RProof.RowShape @RProof.ExtremeSelectedData) : SM.hyp_R :=
  SM.sm_R_of_cv_R (RProof.cv_R_of_rows h174 h175 h176 h177)

end Bridge

/-! ## 5. Row 184 SM:corner_laws_and_soft — the final theorem (TARGETS.md "Exact final target")

"Prove that the corner state sum C of SM def:C satisfies every wall law on the domains of SM
cor:A-lawful, together with SM thm:C-soft in every soft sector. … Define its conclusion as the
conjunction of these actual C identities, with their printed quantifiers, signs and domains. Do not
replace it by a theorem about a freely supplied lawful function. … It must not retain an R assumption."

The accepted identities enter as their accepted bundles (`CChamberData`, `CSilentData`, `CS3Data`,
`CS5Data`, the Prop `hyp_R`), rows 110/112 as the corner lane's FINAL bundles (`CS7Data`, `CSoftData`),
and the identities inherited through cor:C-inherits (row 128, comparison lane — no final shape yet) as
Props in the shape of cor:A-lawful's accepted `ALawfulData` fields with `cornerStateSum` for `amplitude`
(TO BE UNIFIED WITH THE COMPARISON LANE: the field TYPES change, not the theorem). -/

namespace SM

open WallGerm SoftDuplication

/-- cor:C-inherits' cusp law (sm-6:313-319): "C(P_loop) − C(P_no) = −κ C(P(0) ∖ j)" on cor:A-lawful's
domain ("when the deletion satisfies (G1)"), the deletion generic (the domain check of the printed
proof, sm-6:335-359, existential), including threaded cusps (no emptiness hypothesis). -/
def CuspLawC : Prop :=
  ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j),
    G1 (deleteVertex w.center j) →
    ∃ hQ : Generic (deleteVertex w.center j),
    ∃ b : Bool, CuspCase w.center j b ∧ (∀ b' : Bool, CuspCase w.center j b' → b' = b) ∧
      ∃ κ : ℤ, (κ = -1 ∨ κ = 1) ∧
        ∀ s t : w.SideParameter,
          (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
            rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val = (κ : ℝ)) ∧
          cornerStateSum (by have := hf.1; omega) (w.sideTuple (w.cuspLoopSide b j) s).property -
              cornerStateSum (by have := hf.1; omega) (w.sideTuple (!(w.cuspLoopSide b j)) t).property =
            -κ * cornerStateSum (by have := hf.1; omega) hQ

/-- cor:A-lawful's reversal identity inherited by `C`: `C(P̄) = (−1)^n C(P)` (`generic_reversal`, accepted). -/
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

/-- Proposed bundle of row 128 cor:C-inherits (comparison lane; TO BE UNIFIED): "Under Hypothesis R, C
satisfies every identity of cor:A-lawful on the domains stated there" — `ALawfulData` with
`cornerStateSum` for `amplitude`, minus `root_independent` (A-specific, no C analogue) and minus the
A-specific "every induced root" sub-clause of the cusp law; the vertex-edge, triple and soft fields are
the row bundles themselves. -/
structure CInheritsData : Prop where
  shift_invariant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (k : ZMod n), cornerStateSum hn ((generic_shift k P).mpr hP) = cornerStateSum hn hP
  descends : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n), ∃ C' : GenericPolygon n → ℤ,
    ∀ P : GenericTuple n, C' (polygonProjection P) = cornerStateSum hn P.property
  chamber_constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    (Q ∈ labelledChamber P → cornerStateSum hn Q.property = cornerStateSum hn P.property) ∧
    (polygonProjection Q ∈ chamber (polygonProjection P) →
      cornerStateSum hn Q.property = cornerStateSum hn P.property)
  silent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n),
    (∀ M a : ZMod n, w.ExtensionAt M a → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property) ∧
    (∀ i j k : ZMod n, w.PureCutAt i j k → ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property = cornerStateSum hn (w.sideTuple false s).property)
  flat_law : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j),
    ∃ hQ : Generic (deleteVertex w.center j),
    ∀ (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0),
      turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
      cornerStateSum (by have := hf.1; omega) (w.generic_punctured sRight hRight0) -
        cornerStateSum (by have := hf.1; omega) (w.generic_punctured sLeft hLeft0) =
        cornerStateSum (by have := hf.1; omega) hQ
  cusp_law : CuspLawC
  vertex_edge_law : CS7Data
  triple_law : hyp_R
  soft_theorem : CSoftData
  reversal_law : ReversalLawC
  triangles : TrianglesC

/-- PLACEHOLDER for the comparison lane's row 128 (FIXED name `SM.cor_C_inherits`; hyp:R in
`explicit_parameter` mode). -/
theorem cor_C_inherits (_hR : hyp_R) : CInheritsData := by
  sorry

/-- **Row 184, the statement** (FIXED name `SM.corner_laws_and_soft : CornerLawsAndSoftData`): the
conjunction of the actual `C` identities, one field per item of TARGETS' "Required coverage", each on its
printed domain, with no R parameter. -/
structure CornerLawsAndSoftData : Prop where
  /-- "Chamber constancy" — prop:C-chamber (accepted) -/
  chamber : CChamberData
  /-- "and silent-wall invariance" — prop:C-silent (E) and (C) (accepted) -/
  silent : CSilentData
  /-- "The flat deletion law" — thm:C-S3 (accepted) -/
  flat : CS3Data
  /-- "Both bigon branches and the sliding branch of the vertex-edge law, with the stated sign and the
  actual two child polygons" — thm:C-S7 (`VertexEdgeAt` is bigon ∨ sliding, `vertexEdge_bigon_or_sliding`) -/
  vertex_edge : CS7Data
  /-- "Triple-wall invariance at every source simple triple wall, after proving R" — hyp:R, PROVED
  (Bridge:theorem), no R assumption retained -/
  triple : hyp_R
  /-- "The full cusp jump on the source domain (the deletion satisfies G1), including threaded cusps" —
  cor:C-inherits' cusp law -/
  cusp : CuspLawC
  /-- "retain the direct empty-cusp zero result" — thm:C-S5 (accepted) -/
  empty_cusp : CS5Data
  /-- "The soft theorem in every sector, including zero-selector sectors" — thm:C-soft -/
  soft : CSoftData
  /-- "the normalizations and reversal/cyclic identities inherited with cor:A-lawful": reversal -/
  reversal : ReversalLawC
  /-- — cyclic (def:C's cyclic quotient, accepted `cornerStateSum_genericShift`) -/
  cyclic : CyclicLawC
  /-- — the triangle normalizations -/
  triangles : TrianglesC

/-- **Row 184 modulo hyp:R, rows 110, 112 and 128**, PROVED from the accepted rows prop:C-chamber,
prop:C-silent, thm:C-S3, thm:C-S5 and def:C's cyclic invariance.  No R parameter remains in the row:
`hR` is discharged by `Bridge.sm_R`. -/
theorem corner_laws_and_soft_of (hR : hyp_R) (h7 : CS7Data) (hs : CSoftData) (hinh : CInheritsData) :
    CornerLawsAndSoftData where
  chamber := prop_C_chamber
  silent := prop_C_silent
  flat := thm_C_S3
  vertex_edge := h7
  triple := hR
  cusp := hinh.cusp_law
  empty_cusp := thm_C_S5
  soft := hs
  reversal := hinh.reversal_law
  cyclic := fun _ _ hn P a => cornerStateSum_genericShift hn a P
  triangles := hinh.triangles

/-- **Row 184, SM:corner_laws_and_soft** (FIXED name): "the final assembly instantiates that conditional
theorem with the separately proved R result" (TARGETS.md). -/
theorem corner_laws_and_soft : CornerLawsAndSoftData :=
  corner_laws_and_soft_of Bridge.sm_R thm_C_S7 thm_C_soft (cor_C_inherits Bridge.sm_R)

end SM
