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

/-! ### Unit U-176 (prefix `est_`) — R:extreme_transport: interface Props, ledger, realisation status

Written 2026-09-15 by the U-176 prover. Source: reference/R/RA/R_EXTREME_SINGLETON_TRANSPORT_PROOF.md
("Statement and canonical data", §1–§4). Pattern (PLAN_FINAL §4 174/176/177, D-F11): the RII port
relation and the diagram identifications the printed proof establishes by geometry are stated as an
explicit INTERFACE (`est_PortData` per affected carrier, `est_port_relation` over the event data); the RA
ledger — lem:fulltwist (`CV.fulltwist_coefficient`), lem:homflyrows (ii) (`CV.homflyrows.two_component_row`),
the floor `CV.CarrierSlotFloor` at the two clean outer carriers, knot parity through `mindegAZ_mul`, and the
carrier-by-carrier transport of the unaffected carriers (`EXT_homfly_wall`) — is PROVED from it
(`est_ledger`). The interface is never mapped. -/

section EST

open SM.Carrier SM.Link

/-! #### A. Laurent-ring bookkeeping for (11) and (16) -/

/-- `(p − q)_d = p_d − q_d` in `ℤ[a^{±1}]`. -/
theorem est_coeff_sub (p q : LaurentPolynomial ℤ) (d : ℤ) : (p - q).coeff d = p.coeff d - q.coeff d := by
  simp

/-- (16): "Extracting the two monomials of `a − a^{-1}`" from the `[z^{-1}]` row (11)
`[z^{-1}] P(D_A) = (a − a^{-1}) a^{-2ℓ} [z^0] G`: `[a^{s-1} z^{-1}] P(D_A) = [a^{s-2+2ℓ}] G − [a^{s+2ℓ}] G`. -/
theorem est_coeffAt_of_zRow (F G : R) (s ℓ : ℤ)
    (h : zRow (-1) F = (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * zRow 0 G) :
    coeffAt (s - 1) (-1) F = coeffAt (s - 2 + 2 * ℓ) 0 G - coeffAt (s + 2 * ℓ) 0 G := by
  rw [← coeff_zRow, h, sub_mul, sub_mul, est_coeff_sub, mul_assoc, mul_assoc,
    coeff_T_mul', coeff_T_mul', coeff_T_mul', coeff_T_mul', coeff_zRow, coeff_zRow]
  congr 2 <;> ring

/-- "Therefore `f_1 f_2` has no `a`-exponent below `D`" (§3): a coefficient of a product of two nonzero
Laurent polynomials below the sum of their floors vanishes (`mindegAZ_mul`, the corner lane's FR-CC-3 route). -/
theorem est_coeffAt_mul_eq_zero (f g : R) (hf : f ≠ 0) (hg : g ≠ 0) (a b d : ℤ)
    (ha : a ≤ mindegAZ f) (hb : b ≤ mindegAZ g) (hd : d < a + b) : coeffAt d 0 (f * g) = 0 := by
  by_contra hne
  have := (mindegAZ_spec (mul_ne_zero hf hg)).2 d 0 hne
  rw [mindegAZ_mul hf hg] at this
  omega

/-! #### B. The def:X1 data of a carrier read on its grouped diagram `D(W) = carrierDiagram`
(cor:groupedknot (B), `GT_groupedPoly_eq_homfly`): `w(D) = w_{S,L}`, `R(Γ_D) = R(L)`, `d(D) = slot`,
`Ω(D) = Ω₁(S,L)` — the "two bindings agree" sentence of lem:fulltwist (d6:2020–2022). -/

/-- `w(D(W)) = w_{S,L}` (def:positive-lift: the writhe of the positive lift is its crossing count;
`groupedWrithe_eq_card_geoCarrierCrossings`). -/
theorem est_carrierDiagram_writhe (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierDiagram hn hG hS q).writhe = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS q]
  exact geoPositiveLift_writhe hn _ _ q

/-- `d(D(W)) = 1 − w_{S,L} − R(L) = slot` (`absRot` of the lift IS `carrierR`: the unique component of the
lift is the corner polygon, `geoPositiveLift_comp`, definitionally). -/
theorem est_carrierDiagram_d (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    CV.d (CV.carrierDiagram hn hG hS q) rfl = CV.slot hn hG hS q := by
  unfold CV.d CV.slot
  rw [est_carrierDiagram_writhe]
  rfl

/-- `Ω(D(W)) = Ω₁(S,L)`. -/
theorem est_carrierDiagram_Omega (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    CV.Omega (CV.carrierDiagram hn hG hS q) rfl = CV.Omega1 hn hG hS q := by
  unfold CV.Omega CV.Omega1
  rw [est_carrierDiagram_d, GT_groupedPoly_eq_homfly]

/-! #### C. The interface: the RII port relation and the auxiliary components (§1–§3 of the RA text)

For one row `j` of the full-availability fibre, `q` the affected carrier of `S = Q ∪ {j}` on the `K3`
side `H` (its grouped diagram `D_0 = carrierDiagram q`, "clean": the two other triangle crossings are
dominated), `q'` its copy on the empty side `L` (grouped diagram `D_+ = carrierDiagram q'`, which
retains the two other triangle crossings as "the two positive self-crossings `q, r`"), and `y` the lift
crossing of the one to be switched ("`q`" of the text). -/

/-- **The RII port data of an affected singleton carrier** (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md §1–§3),
field by field: (T2) "Switching `q` makes it negative; the adjacent local port pairs then make `q, r` an
empty opposite-sign oriented RII pair. Deleting it leaves exactly `D_0`" (`port`); (T1) "`D_A =
smooth_q(D_+)`" (`smooth`), "Smoothing `q` splits `D_+` into two components" (`two`, `i`, `j`); (9a)/(10)
"the exact component data" — the two components have the polynomials of the two clean outer carriers
`Λ₁, Λ₂` of the full support `S_full = Q ∪ {x, y, z}` on `L` (`Sf`, `poly₁`, `poly₂`: cor:groupedknot (A)(B),
lc:single-crossing for the kink `r`); "`ell` the linking number of the two components" (`link`); (14)
`w_0 = w_1 + w_2 + 2ℓ` (`writhe`); (13) `R_1 + R_2 + 1 = R` (`rot`, turnlift (ii) + the corner ledger (12));
(12) each clean outer carrier is uniform or exactly one-dissent after a possible reversal (`alt₁`, `alt₂`). -/
structure est_PortData (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) where
  /-- (T2) the RII port relation: the switched `D_+` is carried to `D_0` by oriented RII moves -/
  port : Relation.ReflTransGen RII ((CV.carrierDiagram hn hG' hS' q').switch y) (CV.carrierDiagram hn hG hS q)
  /-- `D_A = smooth_q(D_+)` -/
  DA : Diagram
  /-- (T1) -/
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  /-- "Smoothing `q` splits `D_+` into two components" -/
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  /-- `S_full = Q ∪ {x, y, z}`, "an independent `L`-side support" -/
  Sf : Finset (Crossing P')
  hSf : Sf ∈ CV.Ind hG'.crossingGeometry
  /-- the two clean outer carriers of (10) -/
  Λ₁ : GeoComponent hG'.crossingGeometry Sf
  Λ₂ : GeoComponent hG'.crossingGeometry Sf
  /-- (9a) "polynomials `(Q_C, Q_B)`" (resp. `(Q_A, Q_B)`, `(Q_C, Q_A)`) -/
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  /-- "`ell` … the linking number of the two components" -/
  ℓ : ℤ
  link : CV.IsLinkingNumber DA i j ℓ
  /-- (14) `w_0 = w_1 + w_2 + 2ℓ` -/
  writhe : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ + 2 * ℓ
  /-- (13) `R_1 + R_2 + 1 = R` -/
  rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1
  /-- (12) "each clean outer carrier … is exactly one-dissent, never uniform with the wrong sign" -/
  alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁)
  alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)

/-! #### D. The ledger of the affected carrier: (7), (8), (11), (15), (16) -/

/-- **(16) `Ω_+ = Ω_0`**: from the port data, `w_+ = w_0 + 2` and `R(D_+) = R(D_0)` (7), lem:fulltwist gives
`Ω_+ − Ω_0 = [a^{d_0 − 1} z^{-1}] P(D_A)` (8); lem:homflyrows (ii) with knot parity gives the `[z^{-1}]`
row (11); the two extracted monomials sit at `a^{D−4}` and `a^{D−2}` with `D = d_1 + d_2 = d_0 + 2 + 2ℓ` (15),
below the floor `D` of `f_1 f_2` (thm:carrierfloor (C)+(D) at the two clean outer carriers, `CarrierSlotFloor`
+ `mindegAZ_mul`): both vanish. "The last equality is exactly the floor, not an assumed sharpness statement." -/
theorem est_omega1_eq_of_port (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)
    (D : est_PortData hn hG hG' hS hS' q q' y)
    (hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q + 2)
    (hR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q) :
    CV.Omega1 hn hG' hS' q' = CV.Omega1 hn hG hS q := by
  have hpos : (CV.carrierDiagram hn hG' hS' q').IsPositive y := geoPositiveLift_isPositive hn _ _ q' y
  -- (7) `d_+ = d_0 − 2`
  have hd : CV.d (CV.carrierDiagram hn hG' hS' q') rfl = CV.d (CV.carrierDiagram hn hG hS q) rfl - 2 := by
    rw [est_carrierDiagram_d, est_carrierDiagram_d]
    unfold CV.slot
    rw [hw, hR]; ring
  -- (8) lem:fulltwist
  have hft := CV.fulltwist_coefficient (CV.carrierDiagram hn hG hS q) (CV.carrierDiagram hn hG' hS' q')
    D.DA y hpos D.smooth D.port rfl rfl hd
  rw [est_carrierDiagram_Omega, est_carrierDiagram_Omega, est_carrierDiagram_d] at hft
  -- (11) lem:homflyrows (ii)
  have hrow := CV.homflyrows.two_component_row D.DA D.i D.j D.two D.ij D.ℓ D.link
  rw [D.poly₁, D.poly₂] at hrow
  have hcoef := est_coeffAt_of_zRow _ _ (CV.slot hn hG hS q) D.ℓ hrow
  -- the floor at the two clean outer carriers
  have hne₁ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₁
  have hne₂ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₂
  have h₁ := hF hn hG' D.hSf D.Λ₁ D.alt₁
  have h₂ := hF hn hG' D.hSf D.Λ₂ D.alt₂
  -- (15) `D = d_0 + 2 + 2ℓ`
  have hsum : CV.slot hn hG' D.hSf D.Λ₁ + CV.slot hn hG' D.hSf D.Λ₂ =
      CV.slot hn hG hS q + 2 + 2 * D.ℓ := by
    unfold CV.slot
    have := D.writhe
    have := D.rot
    omega
  -- (16)
  have hz₁ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q - 2 + 2 * D.ℓ) h₁ h₂ (by omega)
  have hz₂ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q + 2 * D.ℓ) h₁ h₂ (by omega)
  rw [hcoef, hz₁, hz₂, sub_zero] at hft
  linarith

/-! #### E. The event-level configuration of a singleton row (R-LOC-2, R-PAR, the sign radius)

Side `t` is the `K3` side `H` (`CompleteLocal`), `t'` the empty side `L`; `j` the selected triangle
crossing, `u, v` the two others; `S = Q ∪ {j}`, `S' = transportSupport hs S`. -/

section ESTEvent

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- Three distinct triangle crossings exhaust the triangle. -/
theorem est_tri_exhaust {t : E.Parameter} (hef' : IsCrossing (E.curve t) {e, f})
    (heg' : IsCrossing (E.curve t) {e, g}) (hfg' : IsCrossing (E.curve t) {f, g})
    {j u v : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (c : Crossing (E.curve t)) (hc : c.val ∈ triangleSupports e f g) : c = j ∨ c = u ∨ c = v := by
  rcases GT_tri_cases t hef' heg' hfg' j hj with hj' | hj' | hj' <;>
  rcases GT_tri_cases t hef' heg' hfg' u hu with hu' | hu' | hu' <;>
  rcases GT_tri_cases t hef' heg' hfg' v hv with hv' | hv' | hv' <;>
  first
  | exact absurd (hj'.trans hu'.symm) hju
  | exact absurd (hj'.trans hv'.symm) hjv
  | exact absurd (hu'.trans hv'.symm) huv
  | (rcases GT_tri_cases t hef' heg' hfg' c hc with h | h | h <;> first
      | exact Or.inl (h.trans hj'.symm)
      | exact Or.inr (Or.inl (h.trans hu'.symm))
      | exact Or.inr (Or.inr (h.trans hv'.symm)))

/-- On the `K3` side any two distinct triangle crossings interlace. -/
theorem est_interlaces_of_complete {t : E.Parameter} (ht : t.val ≠ 0)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht) hef' heg' hfg')
    {u v : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (huv : u ≠ v) : GeometricInterlaces (geomAt E t ht) u v := by
  obtain ⟨hAB, hAC, hBC⟩ := hcomp
  rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl <;>
  rcases GT_tri_cases t hef' heg' hfg' v hv with rfl | rfl | rfl <;>
  first
  | exact absurd rfl huv
  | exact hAB
  | exact hAC
  | exact hBC
  | exact geometricInterlaces_symm _ hAB
  | exact geometricInterlaces_symm _ hAC
  | exact geometricInterlaces_symm _ hBC

/-- A crossing of `S = Q ∪ {j}` in the triangle is `j`. -/
theorem est_eq_j_of_mem_S_T {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) {j c : Crossing (E.curve t)}
    (hcS : c ∈ Q ∪ {j}) (hcT : c.val ∈ triangleSupports e f g) : c = j := by
  rcases Finset.mem_union.mp hcS with h | h
  · exact absurd ((F1.mem_triangleCrossings e f g c).mpr hcT)
      (Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 h)
  · exact Finset.mem_singleton.mp h

/-- `S = Q ∪ {j}` is independent (full availability; `PRE_union_mem_Ind_of_fullAvail`). -/
theorem est_S_ind {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) (hfull : FullAvail (geomAt E t ht) e f g Q)
    {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g) :
    Q ∪ {j} ∈ CV.Ind (geomAt E t ht) :=
  PRE_union_mem_Ind_of_fullAvail hQ hfull
    (Finset.singleton_subset_iff.mpr ((F1.mem_triangleCrossings e f g j).mpr hj))
    (PRE_mem_Ind_of_card_le_one _ (by rw [Finset.card_singleton]))

/-- `S' = Q' ∪ {j'}` is independent on the far side (`Q'` outside with full availability, R-LOC-2 (4)). -/
theorem est_S'_ind (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    transportSupport hs (Q ∪ {j}) ∈ CV.Ind (geomAt E t' ht'.1) := by
  rw [GT_transportSupport_S]
  exact est_S_ind ht'.1 (GT_outsideSupports_transport hL ht ht' hop hs hQ)
    (GT_fullAvail_transport hL ht ht' hop hs hQ hfull) hj

/-- **The wall data of a singleton row** `S = Q ∪ {j}` (as `GT_Endpoint.wall`: the only triangle crossing
of `S` is `j`, so no two corners form a reversed pair). -/
theorem est_wall (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    GT_Wall (geomAt E t ht.1) (geomAt E t' ht'.1) hs (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) where
  indep := CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj)
  indep' := CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)
  key_lt v w hvw := AV_key_lt_of_gauss _ _ hs hef heg hfg (hL.gauss_words t t' ht ht' hop hs) v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvS, hwS⟩
    have h1 := est_eq_j_of_mem_S_T ht.1 hQ hvS ((F1.mem_triangleCrossings e f g v.1).mp hrev.1)
    have h2 := est_eq_j_of_mem_S_T ht.1 hQ hwS ((F1.mem_triangleCrossings e f g w.1).mp hrev.2.1)
    exact hrev.2.2.1 (h1.trans h2.symm)
  turn_eq := hR.turn_eq t t' ht ht'
  sign_eq := hR.sign_eq t t' ht ht'
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
    rw [(hr t' ht' h).2, (hr t ht h).2]

/-- On `H` the two unselected triangle crossings are dominated by `j` ("the other two local crossings are
dominated"). -/
theorem est_not_mem_U_H {t : E.Parameter} (ht : t.val ≠ 0)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) {j u : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) : u ∉ CV.U (geomAt E t ht) (Q ∪ {j}) := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h j (Finset.mem_union_right _ (Finset.mem_singleton_self j))
    (est_interlaces_of_complete ht hcomp hu hj hju.symm)

/-- On `L` the two unselected triangle crossings survive ("On `L` they survive as the two positive
self-crossings `q, r`"): `u' ∉ S'`, `u'` interlaces neither `j'` (empty local graph, R-LOC-2 corollary) nor
any member of `Q'` (full availability, R-LOC-2 (4)). -/
theorem est_mem_U_L (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) :
    crossingTransport hs u ∈ CV.U (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rw [CV.mem_U_iff]
  constructor
  · rw [mem_transportSupport_iff]
    intro huS
    exact hju (est_eq_j_of_mem_S_T ht.1 hQ huS hu).symm
  · intro x' hx'
    obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
    rw [mem_transportSupport_iff] at hx'
    rcases Finset.mem_union.mp hx' with hxQ | hxj
    · have hxT : x.val ∉ triangleSupports e f g := fun h =>
        Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hxQ
          ((F1.mem_triangleCrossings e f g x).mpr h)
      rw [hL.interlace_toggle t t' ht ht' hop hs u x, L.xor_iff_of_not_right (fun h => hxT h.2.2)]
      have huA : u ∈ avail (geomAt E t ht.1) e f g Q := by
        rw [hfull]; exact (F1.mem_triangleCrossings e f g u).mpr hu
      exact fun h => ((F1.mem_avail _ e f g Q u).mp huA).2 x hxQ (geometricInterlaces_symm _ h)
    · obtain rfl := Finset.mem_singleton.mp hxj
      rw [hL.complement_on_triangle t t' ht ht' hop hs u x hu hj hju.symm]
      exact fun h => h (est_interlaces_of_complete ht.1 hcomp hu hj hju.symm)

end ESTEvent

/-! #### F. Retained crossings across the wall: the common carrier, the spectators and the affected carrier

(5)/(§1): on `H` the two unselected local crossings `u, v` are dominated, so every carrier of `S` retains
only outside crossings; on `L` they are the two positive self-crossings of ONE carrier — the copy of the
carrier `q₀` owning their two visits on the edge they share (adjacent visits, R-LOC-2 (2)). Every other
carrier's retained set is carried by the edge-pair transport. -/

section ESTRetained

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

omit [NeZero n] in
/-- The label shared by two triangle crossings is not a label of the third. -/
theorem est_shared_not_mem_third (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {P : LabelledTuple n}
    {j u v : Crossing P} (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val) : ℓ ∉ j.val := by
  have hmem : ∀ {s : Finset (ZMod n)}, s ∈ triangleSupports e f g →
      s = {e, f} ∨ s = {e, g} ∨ s = {f, g} := by
    intro s hs; simpa [triangleSupports] using hs
  have hju' : j.val ≠ u.val := fun h => hju (Subtype.ext h)
  have hjv' : j.val ≠ v.val := fun h => hjv (Subtype.ext h)
  have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  intro hℓj
  rcases hmem hj with h1 | h1 | h1 <;> rcases hmem hu with h2 | h2 | h2 <;>
    rcases hmem hv with h3 | h3 | h3 <;>
    first
    | exact hju' (h1.trans h2.symm)
    | exact hjv' (h1.trans h3.symm)
    | exact huv' (h2.trans h3.symm)
    | (rw [h1] at hℓj; rw [h2] at hℓu; rw [h3] at hℓv
       simp only [Finset.mem_insert, Finset.mem_singleton] at hℓj hℓu hℓv
       rcases hℓj with rfl | rfl <;> rcases hℓu with h | h <;> rcases hℓv with h' | h' <;>
         first
         | exact hef h | exact hef h' | exact hef h.symm | exact hef h'.symm
         | exact heg h | exact heg h' | exact heg h.symm | exact heg h'.symm
         | exact hfg h | exact hfg h' | exact hfg h.symm | exact hfg h'.symm)

/-- A visit on an edge that is not an edge of `j` is a good mark of `S = Q ∪ {j}` (its reversed partners are
visits of the other triangle crossings, none of which is a corner). -/
theorem est_good_of_edge {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) {j : Crossing (E.curve t)} {w : Visit (E.curve t)}
    (hw : w.2.val ∉ j.val) : GT_Good (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) (Sum.inr w) := by
  intro v' hv' u hrev hu
  obtain rfl := Sum.inr.inj hv'
  have huS : u.1 ∈ Q ∪ {j} := hu
  have huj : u.1 = j := est_eq_j_of_mem_S_T ht hQ huS ((F1.mem_triangleCrossings e f g u.1).mp hrev.2.1)
  apply hw
  rw [hrev.2.2.2, ← huj]
  exact u.2.property

/-- An unselected triangle crossing is not in `S`. -/
theorem est_not_mem_S {t : E.Parameter} (ht : t.val ≠ 0) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht) e f g) {j u : Crossing (E.curve t)}
    (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u) : u ∉ Q ∪ {j} :=
  fun h => hju (est_eq_j_of_mem_S_T ht hQ h hu).symm

/-- On `H` the two visits of `u, v` on their shared edge lie on one carrier of `S` (adjacent visits of two
unselected crossings, `GT_owner_eq_of_adjacent`). -/
theorem est_owner_shared_eq (hL : LocalizationData E e f g δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) {j u v : Crossing (E.curve t)}
    (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v) {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val) :
    geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) =
      geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn v ℓ hℓv)) :=
  GT_owner_eq_of_adjacent _ _ (GT_adjacent_of_shared hL hef heg hfg t ht hu hv huv hℓu hℓv) rfl
    (est_not_mem_S ht.1 hQ hu hju) (est_not_mem_S ht.1 hQ hv hjv)

/-- On `H` no triangle crossing is retained by any carrier of `S`. -/
theorem est_not_retained_H {t : E.Parameter} (ht : Punctured E δ t)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})) {c : Crossing (E.curve t)}
    (hc : c ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q) : c.val ∉ triangleSupports e f g := by
  intro hcT
  have hcU : c ∈ CV.U (geomAt E t ht.1) (Q ∪ {j}) := by
    have := geoCarrierCrossings_subset_U _ (CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj)) q hc
    rw [mem_geoSupportUnselected_iff] at this
    exact (CV.mem_U_iff _ _ c).mpr this
  by_cases hcj : c = j
  · subst hcj
    exact ((CV.mem_U_iff _ _ c).mp hcU).1 (Finset.mem_union_right _ (Finset.mem_singleton_self c))
  · exact est_not_mem_U_H ht.1 hcomp Q hj hcT (Ne.symm hcj) hcU

/-- An outside crossing is retained by the copy of a carrier iff it is retained by the carrier (all its visits
are good marks; `GT_owner_transport`). -/
theorem est_retained_outside_iff (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})) {c : Crossing (E.curve t)}
    (hcT : c.val ∉ triangleSupports e f g) :
    crossingTransport hs c ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) ↔
      c ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hgood : ∀ v : Visit (E.curve t), v.1 = c →
      GT_Good (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) (Sum.inr v) := fun v hv =>
    GT_good_of_not_mem _ _ (by rw [hv]; exact fun h => hcT ((F1.mem_triangleCrossings e f g c).mp h))
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_transportSupport_iff]
  constructor
  · rintro ⟨hcS, hall⟩
    refine ⟨hcS, fun v hv => ?_⟩
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport W (hgood v hv)] at this
    exact (GT_carrierEquiv W).injective this
  · rintro ⟨hcS, hall⟩
    refine ⟨hcS, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hvc : v.1 = c := (crossingTransport hs).injective hw
    rw [← markTransport_visit, GT_owner_transport W (hgood v hvc), hall v hvc]

/-- An unselected triangle crossing `u` is retained on `L` by the copy of `q` iff `q` owns the visit of `u`
on the edge `ℓ` it shares with the other unselected crossing (that visit is good; `u' ∈ U(S')`). -/
theorem est_retained_u_iff (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓj : ℓ ∉ j.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})) :
    crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) ↔
      geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have huU' := est_mem_U_L hL ht ht' hop hs hcomp hQ hfull hj hu hju
  have hgood : GT_Good (triangleCrossings (E.curve t) e f g) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) :=
    est_good_of_edge ht.1 hQ hℓj
  rw [mem_geoCarrierCrossings]
  constructor
  · rintro ⟨-, hall⟩
    have := hall (visitTransport hs (visitOn u ℓ hℓu)) rfl
    rw [← markTransport_visit, GT_owner_transport W hgood] at this
    exact (GT_carrierEquiv W).injective this
  · intro hq
    refine ⟨((CV.mem_U_iff _ _ _).mp huU').1, fun w hw => ?_⟩
    rw [CV.owner_eq_of_mem_U _ (est_S'_ind hL ht ht' hop hs hQ hfull hj) huU' w
      (visitTransport hs (visitOn u ℓ hℓu)) hw rfl, ← markTransport_visit, GT_owner_transport W hgood, hq]

/-- **The retained set of an unaffected carrier is carried** (the common carrier and every spectator). -/
theorem est_retained_eq_of_ne (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hne : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) ≠ q) :
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding := by
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hcT : c.val ∈ triangleSupports e f g
  · have hcH : c ∉ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q :=
      fun h => est_not_retained_H ht hcomp hQ hfull hj q h hcT
    refine iff_of_false ?_ hcH
    rcases est_tri_exhaust hef' heg' hfg' hj hu hv hju hjv huv c hcT with rfl | rfl | rfl
    · intro h
      exact ((mem_geoCarrierCrossings _ _ _ _).mp h).1
        ((mem_transportSupport_iff hs _ c).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self c)))
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q]
      exact hne
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hv hjv hℓv hℓj q,
        ← est_owner_shared_eq hL hef heg hfg ht hQ hu hv hju hjv huv hℓu hℓv]
      exact hne
  · exact est_retained_outside_iff hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hcT

/-- **The retained set of the affected carrier** `q₀` (the owner of the shared-edge visits of `u, v`): the
carried outside survivors together with the two positive self-crossings `u', v'`. -/
theorem est_retained_affected (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q) :
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding ∪
        {crossingTransport hs u, crossingTransport hs v} := by
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_union, Finset.mem_map_equiv, Equiv.symm_apply_apply, Finset.mem_insert, Finset.mem_singleton,
    (crossingTransport hs).injective.eq_iff, (crossingTransport hs).injective.eq_iff]
  by_cases hcT : c.val ∈ triangleSupports e f g
  · have hcH : c ∉ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q :=
      fun h => est_not_retained_H ht hcomp hQ hfull hj q h hcT
    rcases est_tri_exhaust hef' heg' hfg' hj hu hv hju hjv huv c hcT with rfl | rfl | rfl
    · refine iff_of_false ?_ ?_
      · intro h
        exact ((mem_geoCarrierCrossings _ _ _ _).mp h).1
          ((mem_transportSupport_iff hs _ c).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self c)))
      · rintro (h | h | h)
        · exact hcH h
        · exact hju h
        · exact hjv h
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q]
      exact iff_of_true hq (Or.inr (Or.inl rfl))
    · rw [est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hv hjv hℓv hℓj q,
        ← est_owner_shared_eq hL hef heg hfg ht hQ hu hv hju hjv huv hℓu hℓv]
      exact iff_of_true hq (Or.inr (Or.inr rfl))
  · rw [est_retained_outside_iff hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hcT]
    constructor
    · exact Or.inl
    · rintro (h | rfl | rfl)
      · exact h
      · exact absurd hu hcT
      · exact absurd hv hcT

end ESTRetained

/-! #### G. The unaffected carriers ("the common carrier read, every triangle-disjoint spectator read, and
all weights are identical across the wall", §4) and the affected carrier's writhe shift (7) -/

section ESTCarriers

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `P_{S,L}` of an unaffected carrier is carried: its retained crossings are outside crossings whose visit
orders and divide signs are carried, so the two positive lifts are record-isomorphic (`EXT_homfly_wall`,
CV:ax:gausscode). -/
theorem est_groupedPoly_eq_of_ne (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hne : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) ≠ q) :
    CV.groupedPoly hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      CV.groupedPoly hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hX := est_retained_eq_of_ne hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hne
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
  · intro v w hv _
    have hvT := est_not_retained_H ht hcomp hQ hfull hj q hv
    exact W.key_lt v w (GT_not_rev_of_not_mem_left
      (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
  · intro v _
    exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

/-- `Ω₁(S,L)` of an unaffected carrier is carried (`w_{S,L}`, `R(L)`, `P_{S,L}` all carried). -/
theorem est_omega1_eq_of_ne (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hne : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) ≠ q) :
    CV.Omega1 hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      CV.Omega1 hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS,
    est_retained_eq_of_ne hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hne,
    Finset.card_map, GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q,
    est_groupedPoly_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hne]

/-- (7) `w_+ = w_0 + 2`: the affected carrier's copy retains the two extra positive self-crossings `u', v'`. -/
theorem est_groupedWrithe_affected (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    {ℓ : ZMod n} (hℓu : ℓ ∈ u.val) (hℓv : ℓ ∈ v.val)
    (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q) :
    CV.groupedWrithe (genericAt E t' ht'.1)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      CV.groupedWrithe (genericAt E t ht.1) q + 2 := by
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS,
    est_retained_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq,
    Finset.card_union_of_disjoint, Finset.card_map, Finset.card_pair ((crossingTransport hs).injective.ne huv)]
  · push_cast; ring
  · rw [Finset.disjoint_left]
    intro c' hc' hcuv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hc'
    have hcT := est_not_retained_H ht hcomp hQ hfull hj q hc
    rcases Finset.mem_insert.mp hcuv with h | h
    · exact hcT (((crossingTransport hs).injective h) ▸ hu)
    · exact hcT (((crossingTransport hs).injective (Finset.mem_singleton.mp h)) ▸ hv)

end ESTCarriers

/-! #### H. The interface Prop and the ledger -/

/-- The crossing of the grouped diagram `D(W)` sitting at a retained crossing `c` of the carrier
(`geoCarrierCrossingEquiv`, def:positive-lift). -/
noncomputable def est_liftCrossing (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry S q) :
    (CV.carrierDiagram hn hG hS q).Γ.Crossing :=
  (geoCarrierCrossingEquiv hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CV.geoIndependent_of_mem_Ind _ hS) q).symm ⟨c, hc⟩

/-- **The RII port relation of row 176 — INTERFACE Prop (D-F11), never mapped.** For every simple RIII
event, radius carrying R-LOC-2 and the sign data, `K3` side `t`, empty side `t'`, outside support `Q` at
full availability, selected triangle crossing `j` and affected carrier `q` of `Q ∪ {j}` (its copy on `L`
retains one of the two other triangle crossings), there is a choice `u` of the retained unselected crossing
whose lift crossing carries the port data `est_PortData` (§1–§3 of the RA text: the RII port relation after
the switch, the two-component smoothing and its exact owner map, the linking number, the writhe and rotation
ledgers (13)/(14), the one-dissent sign ledger (12)). This is the G10-scale geometric content of row 176. -/
def est_port_relation : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (est_PortData hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

section ESTLedger

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- Two present rows with equal selectors and a carrier bijection carrying `Ω₁` are equal
(`rowTerm_of_mem_Ind`, `Fintype.prod_equiv`; the `Ω₁`-only form of `AV_rowTerm_eq_of_summandTransport`,
since `P_{S,L}` and `w_{S,L}` of the affected carrier are NOT carried). -/
theorem est_rowTerm_eq_of_omega (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (hwind : CV.wind hG'.crossingGeometry S' = CV.wind hG.crossingGeometry S)
    (τ : GeoComponent hG.crossingGeometry S ≃ GeoComponent hG'.crossingGeometry S')
    (hΩ : ∀ q, CV.Omega1 hn hG' hS' (τ q) = CV.Omega1 hn hG hS q) :
    rowTerm hn hG S = rowTerm hn hG' S' := by
  rw [rowTerm_of_mem_Ind hn hG hS, rowTerm_of_mem_Ind hn hG' hS', hwind]
  congr 1
  exact Fintype.prod_equiv τ _ _ fun q => (hΩ q).symm

/-- The two other triangle crossings of a selected one. -/
theorem est_others {t : E.Parameter}
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) {j : Crossing (E.curve t)} (hj : j.val ∈ triangleSupports e f g) :
    ∃ u v : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ v.val ∈ triangleSupports e f g ∧
      j ≠ u ∧ j ≠ v ∧ u ≠ v := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl
  · exact ⟨_, _, h2, h3, n12, n13, n23⟩
  · exact ⟨_, _, h1, h3, n12.symm, n23, n13⟩
  · exact ⟨_, _, h1, h2, n13.symm, n23.symm, n12⟩

/-- **The singleton row is carried, `t` the `K3` side** (§4 of the RA text: "Multiplying these equalities
proves all three identities (2), including selector-zero, coefficient-zero, empty-carrier, `ell = 0`, and
`C_Q = 0` cases. No factor was cancelled or divided out."): the selector is carried (`GT_wind_eq`), the
carriers correspond (`GT_carrierEquiv`), every unaffected carrier's `Ω₁` is carried (`est_omega1_eq_of_ne`)
and the affected carrier's by the port ledger (`est_omega1_eq_of_port`). -/
theorem est_row_H (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  refine est_rowTerm_eq_of_omega hn _ _ hS hS'
    (GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W) (GT_carrierEquiv W) fun q => ?_
  obtain ⟨u, v, hu, hv, hju, hjv, huv⟩ := est_others hef' heg' hfg' hj
  obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  by_cases hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q
  · -- the affected carrier: the port ledger
    have hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv W q) :=
      (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mpr hq
    obtain ⟨u₁, -, -, hu₁', ⟨D⟩⟩ := hport n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
      hcomp Q hQ hfull j hj q ⟨u, hu, hju.symm, hu'⟩
    exact est_omega1_eq_of_port hF hn _ _ hS hS' q _ _ D
      (est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq)
      (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q)
  · exact est_omega1_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- **The singleton row is carried, either side extreme** ("separately and without a symmetry assumption",
symmetric in the sides): the `K3` side directly, the empty side by applying the `K3` case to `(t', t)`
(`graphs_complementary`). -/
theorem est_row (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hext : ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rcases hext with hcomp | hemp
  · exact est_row_H hF hport hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj
  · have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
    have hop' : OppositeSides E t' t := by
      unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
    obtain ⟨hef'', heg'', hfg''⟩ := hL.triangle_crossings t' ht'
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef'' heg'' hfg'' :=
      (PRE_176_graphs_complementary hL t' t ht' ht hop' hef'' heg'' hfg'' hef' heg' hfg').mpr hemp
    have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
    have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
    have hj' : (crossingTransport hs j).val ∈ triangleSupports e f g := hj
    have h := est_row_H hF hport hn hL hR hef heg hfg ht' ht hop' hs' hcomp' hQ' hfull' hj'
    rw [← GT_transportSupport_S hs Q j, EXT_transportSupport_symm hs (Q ∪ {j})] at h
    exact h.symm

/-- **The bundle of row 176 from the interface and the floor**: the three PRE fields (accepted) and the
three transports (2) at `x = x_ef`, `y = x_eg`, `z = x_fg`. -/
theorem est_extremeTransportData (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : ExtremeTransportData hn E e f g δ where
  singleton_rows_present := PRE_176_singleton_rows_present E e f g δ
  graphs_complementary := PRE_176_graphs_complementary hL
  sign_branch := PRE_176_sign_branch hGT
  transport_x := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    est_row hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
  transport_y := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    est_row hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
  transport_z := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    est_row hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl)))

end ESTLedger

/-- **The RA ledger of row 176 (U-176)**: `R:extreme_transport` in the fixed row shape from
`CV.CarrierSlotFloor` (thm:carrierfloor (C)+(D) in def:X1's symbols, §1.3) and the RII port relation
interface `est_port_relation`; the radius is the common radius of rows 164 (`localization`), 172
(`generic_table`) and the sign data (`AV_exists_eventRadius`), exactly as the accepted row 173. PROVED. -/
theorem est_ledger (hF : CV.CarrierSlotFloor) (hport : est_port_relation) :
    RowShape @ExtremeTransportData := by
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
  exact est_extremeTransportData hF hport hn hL' hGT' hR' hef heg hfg

/-- The row statement itself from the ledger (the shape of the leaf below). PROVED. -/
theorem est_extreme_transport_of (hF : CV.CarrierSlotFloor) (hport : est_port_relation) (hn : 3 ≤ n)
    (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ :=
  est_ledger hF hport n hn E e f g h3 h4e h4f h4g hE

/-! #### I. Consistency of the interface (sanity, for the realiser) -/

/-- Writhe consistency of the port relation (T2): switching the positive crossing `y` of `D_+` drops the
writhe by `2`, so the switched diagram has writhe `w_+ − 2 = w_0` — as it must, RII moves preserving the
writhe (`switch_writhe`, `geoPositiveLift_sign`). -/
theorem est_switch_writhe (hn : 3 ≤ n) {P' : LabelledTuple n} (hG' : CV.Generic P') {S' : Finset (Crossing P')}
    (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) :
    ((CV.carrierDiagram hn hG' hS' q').switch y).writhe = CV.groupedWrithe hG' q' - 2 := by
  rw [Diagram.switch_writhe, est_carrierDiagram_writhe, geoPositiveLift_sign]
  rfl

end EST

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
