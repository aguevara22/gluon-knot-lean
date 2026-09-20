import RProof.X1Rows
import RProof.X1Rows2
import RProof.GenericTransport
import CV.Rounding
import CV.Curl
import CV.UniformRot
import CV.ChamberInvRow
import CV.GroupedKnot
import CV.Axioms
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

/-! ### Unit U-177 (prefix `esc_`) — the interface Props and the RA ledger of row 177
(R_EXTREME_SELECTED_COUPLE_PROOF.md §1–§5; PLAN_FINAL §4 "174 / 176 / 177", D-F11 interface-first).

Route.  The `couple` field is reduced, with accepted tools only, to an identity on the single
triangle-touching carrier of the empty row (`rowTerm = exteriorFactor · touchingFactor`, row 168's
`EXT_exteriorFactor_wall` / `EXT_exteriorFactor_eq_base`; `GT_empty_tri_subset` for the uniqueness of the
contact carrier on each side; the `GT_Wall` transports of `wt`, `R(L)`, `w_{S,L}`).  The two
Reidemeister moves of the printed proof — (4) the matched switch + RIII through the wall, (6) the RII
bigon deletion after one smoothing and a matched switch — the one- or three-component identifications of the
double smoothings ((8) and the lowest row (12)), and the carrier split of `Q ∪ T` on the empty side
((14)–(17), the central carrier) are stated as explicit interface Props and NEVER mapped; the ledger
`esc_ledger` proves the row from them and from `CV.CarrierSlotFloor` (the (C)+(D) corollary, §1.3):
(5)/(7) by the two HOMFLY skein equations, (8) by knot parity, (13) → (18)–(20) → (2). -/

section ESC

open SM.Link AddMonoidAlgebra

/-! #### A. Laurent-ring helpers (CV/FullTwist.lean is not imported here; `esc_` copies) -/

/-- Coefficient shift: `[a^d z^k] (c a^p z^q · f) = c · [a^{d−p} z^{k−q}] f`. -/
theorem esc_coeffAt_single_mul (d k p q c : ℤ) (f : R) :
    coeffAt d k (single (p, q) c * f) = c * coeffAt (d - p) (k - q) f := by
  unfold coeffAt
  rw [coeff_single_mul_apply]
  congr 2
  ext <;> simp [neg_add_eq_sub]

theorem esc_a_mul_a : R.a * R.a = (single (2, 0) 1 : R) := by
  rw [R.a, single_mul_single]; norm_num

theorem esc_aInv_mul_aInv : R.aInv * R.aInv = (single (-2, 0) 1 : R) := by
  rw [R.aInv, single_mul_single]; norm_num

/-- `a^{−2} z^{2} = single (−2, 2) 1`. -/
theorem esc_aInv_aInv_z_z : R.aInv * R.aInv * (R.z * R.z) = (single (-2, 2) 1 : R) := by
  rw [R.aInv, R.z, single_mul_single, single_mul_single, single_mul_single]; norm_num

/-- `(a − a⁻¹)² K = a² K + a⁻² K − 2K` ("Expand `(a−a^(−1))^2=a^2−2+a^(−2)`", ESC §4). -/
theorem esc_sq_expand (K : R) :
    (R.a - R.aInv) ^ 2 * K = single (2, 0) 1 * K + single (-2, 0) 1 * K - (K + K) := by
  have h1 := R.a_mul_aInv
  rw [← esc_a_mul_a, ← esc_aInv_mul_aInv]
  linear_combination (-2 * K) * h1

/-- The `[a^m z^0]` coefficient of `(a − a⁻¹)² K` samples `K` at `m − 2`, `m`, `m + 2`. -/
theorem esc_coeffAt_sq_mul (m : ℤ) (K : R) :
    coeffAt m 0 ((R.a - R.aInv) ^ 2 * K) =
      coeffAt (m - 2) 0 K + coeffAt (m + 2) 0 K - 2 * coeffAt m 0 K := by
  rw [esc_sq_expand, coeffAt_sub, coeffAt_add, coeffAt_add, esc_coeffAt_single_mul,
    esc_coeffAt_single_mul]
  simp only [one_mul, sub_zero, sub_neg_eq_add]
  ring

/-- `f` lives in the quadrant `a`-degree `≥ m`, `z`-degree `≥ 0` ("no exponent below `d_i` occurs in
`f_i`" together with knot parity). -/
def esc_Quadrant (m : ℤ) (f : R) : Prop := ∀ e ∈ f.coeff.support, m ≤ e.1 ∧ 0 ≤ e.2

theorem esc_Quadrant.coeffAt_eq_zero {m : ℤ} {f : R} (hf : esc_Quadrant m f) {p k : ℤ} (hp : p < m) :
    coeffAt p k f = 0 := by
  by_contra h
  exact absurd (hf (p, k) (Finsupp.mem_support_iff.2 h)).1 (not_le.mpr hp)

theorem esc_quadrant_mul {m n : ℤ} {f g : R} (hf : esc_Quadrant m f) (hg : esc_Quadrant n g) :
    esc_Quadrant (m + n) (f * g) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g he)
  obtain ⟨h1, h2⟩ := hf a ha
  obtain ⟨h3, h4⟩ := hg b hb
  exact ⟨by rw [Prod.fst_add]; omega, by rw [Prod.snd_add]; omega⟩

/-- The corner coefficient of a product of two quadrant elements is the product of the corner
coefficients ("`[a^D]K = omega_A omega_B omega_C`", ESC (19)). -/
theorem esc_coeffAt_corner {m n : ℤ} {f g : R} (hf : esc_Quadrant m f) (hg : esc_Quadrant n g) :
    coeffAt (m + n) 0 (f * g) = coeffAt m 0 f * coeffAt n 0 g := by
  have e : ((m + n, 0) : ℤ × ℤ) = (m, 0) + (n, 0) := by simp
  unfold coeffAt
  rw [e]
  apply coeff_mul_add_of_uniqueAdd
  intro a b ha hb hab
  obtain ⟨h1, h2⟩ := hf a ha
  obtain ⟨h3, h4⟩ := hg b hb
  have e1 := congrArg Prod.fst hab
  have e2 := congrArg Prod.snd hab
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  refine ⟨Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩ <;> simp only <;> omega

/-- Knot parity (CV:ax:homfly, ESC (8)): a one-component diagram has no `z^{−2}` row. -/
theorem esc_knot_coeff_neg_two (J : Diagram) (hJ : J.componentCount = 1) (p : ℤ) :
    coeffAt p (-2) (homfly J) = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := CV.ax_homfly_knot_parity_coeffAt J hJ p (-2) h
  omega

/-- The floor + knot parity of a grouped polynomial as a quadrant (`CarrierSlotFloor`,
`cvt_groupedPoly_inSupportM`): "no exponent below `d_i` occurs in `f_i`". -/
theorem esc_quadrant_groupedPoly (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CV.Generic P) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S)
    (halt : CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q)) :
    esc_Quadrant (CV.slot hn hG hS q) (CV.groupedPoly hn hG hS q) := by
  intro e he
  have hne : coeffAt e.1 e.2 (CV.groupedPoly hn hG hS q) ≠ 0 := Finsupp.mem_support_iff.1 he
  refine ⟨le_trans (hF hn hG hS q halt)
    ((mindegAZ_spec (CV.cvt_groupedPoly_ne_zero hn hG hS q)).2 e.1 e.2 hne), ?_⟩
  obtain ⟨j, hj⟩ := CV.cvt_groupedPoly_inSupportM hn hG hS q e he
  rw [hj]; push_cast; omega

/-! #### B. The contact carrier of the empty row -/

theorem esc_not_triangleDisjoint_iff {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) (e f g : ZMod n) (q : GeoComponent hP S) :
    ¬ TriangleDisjoint hP S e f g q ↔
      ∃ v : Visit P, v.1.val ∈ triangleSupports e f g ∧ geoOwner hP S (Sum.inr v) = q := by
  unfold TriangleDisjoint
  constructor
  · intro h
    by_contra hne
    exact h fun v hv hvq => hne ⟨v, hv, hvq⟩
  · rintro ⟨v, hv, hvq⟩ h
    exact h v hv hvq

/-- "all six visits lie on one `Q`-carrier" (ESC §1): two triangle-touching carriers of the empty row
coincide (`GT_empty_tri_subset`, on either side). -/
theorem esc_contact_unique {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t : E.Parameter} (ht : Punctured E δ t)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {q q' : GeoComponent (geomAt E t ht.1) Q}
    (hq : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q)
    (hq' : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q') : q = q' := by
  obtain ⟨v, hv, hvq⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq
  obtain ⟨v', hv', hvq'⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq'
  have h1 := GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq
  have h2 := GT_empty_tri_subset hL hef heg hfg ht hQ hfull q' hv' hvq'
  have hvT : v.1 ∈ triangleCrossings (E.curve t) e f g := (F1.mem_triangleCrossings e f g v.1).mpr hv
  have hm1 := (mem_geoCarrierCrossings _ Q q v.1).mp (h1 hvT)
  have hm2 := (mem_geoCarrierCrossings _ Q q' v.1).mp (h2 hvT)
  exact (hm1.2 v rfl).symm.trans (hm2.2 v rfl)

/-- The carrier owning the `e`-visit of `x_ef` is triangle-touching. -/
theorem esc_contact_exists {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} {t : E.Parameter}
    (ht : Punctured E δ t) (hef : IsCrossing (E.curve t) {e, f}) (Q : Finset (Crossing (E.curve t))) :
    ∃ q : GeoComponent (geomAt E t ht.1) Q, ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q :=
  ⟨geoOwner _ Q (Sum.inr (visitOn (xPair hef) e (mem_pair_left e f))),
    (esc_not_triangleDisjoint_iff _ _ _ _ _ _).2
      ⟨_, (P1.mem_triangleSupports _).mpr (Or.inl rfl), rfl⟩⟩

/-- A triangle-touching carrier of the empty row owns every visit of every triangle crossing. -/
theorem esc_contact_owns {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t : E.Parameter} (ht : Punctured E δ t)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {q : GeoComponent (geomAt E t ht.1) Q}
    (hq : ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q) :
    triangleCrossings (E.curve t) e f g ⊆ geoCarrierCrossings (geomAt E t ht.1) Q q := by
  obtain ⟨v, hv, hvq⟩ := (esc_not_triangleDisjoint_iff _ _ _ _ _ _).1 hq
  exact GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq

/-- The touching factor of a row with exactly one touching carrier `q₀` is `wt(q₀) Ω₁(S, q₀)`. -/
theorem esc_touchingFactor_eq_of_unique (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n)
    (q₀ : GeoComponent hG.crossingGeometry S)
    (hq₀ : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry S e f g q ↔ q = q₀) :
    touchingFactor hn hG hS e f g = CV.weight hG.crossingGeometry S q₀ * CV.Omega1 hn hG hS q₀ := by
  classical
  unfold touchingFactor
  refine (Finset.prod_congr (s₂ := {q₀}) ?_ fun _ _ => rfl).trans (Finset.prod_singleton _ _)
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact hq₀ q

/-- The touching factor of a row with exactly the four touching carriers `A, B, C, Z`. -/
theorem esc_touchingFactor_eq_of_four (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n)
    (A B C Z : GeoComponent hG.crossingGeometry S)
    (hdist : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z)
    (h : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry S e f g q ↔ (q = A ∨ q = B ∨ q = C ∨ q = Z)) :
    touchingFactor hn hG hS e f g =
      (CV.weight hG.crossingGeometry S A * CV.Omega1 hn hG hS A) *
      (CV.weight hG.crossingGeometry S B * CV.Omega1 hn hG hS B) *
      (CV.weight hG.crossingGeometry S C * CV.Omega1 hn hG hS C) *
      (CV.weight hG.crossingGeometry S Z * CV.Omega1 hn hG hS Z) := by
  classical
  obtain ⟨hAB, hAC, hAZ, hBC, hBZ, hCZ⟩ := hdist
  unfold touchingFactor
  refine (Finset.prod_congr (s₂ := {A, B, C, Z}) ?_ fun _ _ => rfl).trans ?_
  · ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact h q
  · have h1 : A ∉ ({B, C, Z} : Finset (GeoComponent hG.crossingGeometry S)) := by
      simp [hAB, hAC, hAZ]
    have h2 : B ∉ ({C, Z} : Finset (GeoComponent hG.crossingGeometry S)) := by simp [hBC, hBZ]
    have h3 : C ∉ ({Z} : Finset (GeoComponent hG.crossingGeometry S)) := by simp [hCZ]
    rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3, Finset.prod_singleton]
    ring

/-! #### C. Diagram-level helpers: the crossings of the grouped knot diagram, and a crossing carried
through an oriented smoothing at another crossing -/

/-- Every retained crossing `c` of the carrier is a positive crossing of `D(W)` at the double point of
`c` (cor:groupedknot (A) `retain_all`, `geoCarrierCrossingEquiv`). -/
theorem esc_lift_crossing (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.crossingGeometry S q) :
    ∃ x : (CV.carrierDiagram hn hG hS q).Γ.Crossing,
      (CV.carrierDiagram hn hG hS q).Γ.crossingPoint x = crossingPoint c ∧
        (CV.carrierDiagram hn hG hS q).IsPositive x := by
  let hG' := CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn)
  let hT := CV.geoIndependent_of_mem_Ind hG.crossingGeometry hS
  refine ⟨(geoCarrierCrossingEquiv hn hG' hT q).symm ⟨c, hc⟩, ?_,
    geoPositiveLift_isPositive hn hG' hT q _⟩
  have h := crossingPoint_geoCarrierCrossingEquiv hn hG' hT q
    ((geoCarrierCrossingEquiv hn hG' hT q).symm ⟨c, hc⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- A crossing `y ≠ x` of `D` is carried by any oriented smoothing `D₀` of `D` at `x` to a crossing of
`D₀` at the same double point and with the same sign (the outside match `ψ` of the smoothing site). -/
theorem esc_smoothing_outer {D D₀ : Diagram} {x : D.Γ.Crossing} (h : IsOrientedSmoothing D x D₀)
    (y : D.Γ.Crossing) (hyx : y ≠ x) :
    ∃ y₀ : D₀.Γ.Crossing, D₀.Γ.crossingPoint y₀ = D.Γ.crossingPoint y ∧
      (D₀.IsPositive y₀ ↔ D.IsPositive y) := by
  obtain ⟨U, ⟨dat⟩⟩ := h
  have hout : D.Γ.crossingPoint y ∉ interior U := fun hin => hyx ((dat.inner_iff y).mp hin)
  have hU : D.Γ.crossingPoint y ∉ U := by
    intro hin
    have hcl : D.Γ.crossingPoint y ∈ closure U := subset_closure hin
    rw [closure_eq_interior_union_frontier] at hcl
    rcases hcl with h | h
    · exact hout h
    · exact dat.frame.clean.crossingPoint_not_mem_frontier y h
  let yo : D.OuterCrossing U := ⟨y, hout⟩
  refine ⟨(dat.out.ψ yo).1, ?_, ?_⟩
  · have h1 := dat.out.eval_eq (D.outerOverPt yo)
    rw [dat.out.over_eq] at h1
    rw [Diagram.outerOverPt_val, Diagram.outerOverPt_val, Diagram.eval_visitPt, Diagram.eval_visitPt] at h1
    exact h1
  · have hpo : D.Γ.eval (D.outerOverPt yo).1 ∉ U := by
      rw [Diagram.outerOverPt_val, Diagram.eval_visitPt]
      exact hU
    have hpu : D.Γ.eval (D.outerUnderPt yo).1 ∉ U := by
      rw [Diagram.outerUnderPt_val, Diagram.eval_visitPt]
      exact hU
    obtain ⟨l, hl, hdo⟩ := dat.out.dir_pos _ hpo
    obtain ⟨m, hm, hdu⟩ := dat.out.dir_pos _ hpu
    rw [dat.out.over_eq] at hdo
    rw [dat.out.under_eq] at hdu
    have e1 : D₀.Γ.dir (D₀.overStrand (dat.out.ψ yo).1) = l • D.Γ.dir (D.overStrand y) := hdo
    have e2 : D₀.Γ.dir (D₀.underStrand (dat.out.ψ yo).1) = m • D.Γ.dir (D.underStrand y) := hdu
    unfold Diagram.IsPositive
    rw [e1, e2, det_smul_smul]
    exact mul_pos_iff_of_pos_left (mul_pos hl hm)

/-! #### D. The interface Props (D-F11: stated, consumed by the ledger, never mapped) -/

/-- **(4) The matched switch + RIII through the wall** (ESC §2): "switching `x` breaks the cyclic
over-order and makes it transitive … Apply the ordinary oriented RIII change … an isomorphism of the
full oriented traversal records of `D_H^{x-}` and `D_L^{x-}` … `ax:gausscode` identifies their oriented
knots and `ax:homfly` gives `P(D_H^{x-}) = P(D_L^{x-})`", for the crossings `x_H`, `x_L` of the two
grouped contact diagrams at the double points of `x`. -/
def esc_switch_riii (D_H D_L : Diagram) (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing) : Prop :=
  homfly (D_H.switch x_H) = homfly (D_L.switch x_L)

/-- **(6) The RII after one smoothing and a matched switch** (ESC §2): in the oriented smoothings
`D_H^x`, `D_L^x`, "switch `y` … on each side they bound an empty oriented RII bigon. Delete that bigon …
this path extends through the wall as an ambient isotopy from `E_H` to `E_L`. Reidemeister-II invariance
… and isotopy invariance in `ax:homfly` therefore give `P((D_H^x)^{y-}) = P((D_L^x)^{y-})`". -/
def esc_rii_after_smoothing (D_H0 D_L0 : Diagram) (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing) :
    Prop :=
  homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)

/-- **(9)–(11) The three components of the double smoothing `J = D_L^{xy}`** (ESC §3): "The three
components of `J=D_L^{xy}` have successor skeletons `A, C, zBz`" … "the self-crossing knot polynomials
of the first two components in (9) are the grouped full-state polynomials `f_A,f_C`. For the third …
By `cor:groupedknot`, clauses (A) and (B), its grouped knot polynomial is `P_{zBz}(a,0) = P_{ {z} }(a,0)
f_B(a) = f_B(a)`, because the one-crossing positive piece is an unknot"; "Put `Lambda=lk(J)`, the sum
of its three pairwise linking numbers": three components, `2Λ` the total mixed sign sum (mp:lowest's
`twoLambda`), and an indexing of the components by `A, B, C` with the knot polynomials `f_A, f_B, f_C`
(mp:lowest's intrinsic knot diagrams `knotRestrict`). -/
def esc_three_components (J : Diagram) (Λ : ℕ) (fA fB fC : R) : Prop :=
  J.componentCount = 3 ∧ twoLambda J = 2 * (Λ : ℤ) ∧
    ∃ σ : Fin 3 ≃ Fin J.Γ.c, homfly (J.knotRestrict (σ 0)) = fA ∧ homfly (J.knotRestrict (σ 1)) = fB ∧
      homfly (J.knotRestrict (σ 2)) = fC

/-- **(12) The three-component lowest `z`-row, PROVED** from mp:lowest (`SM.lowest.lowest_value` at
`c = 3`; "the exact three-component lowest row `[z^(-2)] P(J) = a^(-2 Lambda) (a-a^(-1))^2 K(a)`",
`K = f_A f_B f_C`): as a coefficient identity, the `a^{−2Λ}` shift written on the right-hand exponent.
The `[z^0]` row of `(a − a⁻¹)² K` is `(a − a⁻¹)² ∏ [z^0] f_i` by knot parity of the three knot
polynomials (`P_knotRestrict_inSupportM_one`, `CV.zRow_zero_mul_of_inSupportM_one`). -/
theorem esc_three_component_row {J : Diagram} {Λ : ℕ} {fA fB fC : R}
    (h : esc_three_components J Λ fA fB fC) (p : ℤ) :
    coeffAt p (-2) (homfly J) = coeffAt (p + 2 * (Λ : ℤ)) 0 ((R.a - R.aInv) ^ 2 * (fA * fB * fC)) := by
  obtain ⟨hc, hΛ, σ, hA, hB, hC⟩ := h
  have hlow := SM.lowest.lowest_value J
  rw [hc, hΛ, P_eq_homfly, show (3 : ℕ) - 1 = 2 from rfl, show (1 : ℤ) - ((3 : ℕ) : ℤ) = -2 by norm_num]
    at hlow
  have hprod : ∏ i : Fin J.Γ.c, zRow 0 (P (J.knotRestrict i)) = zRow 0 fA * zRow 0 fB * zRow 0 fC := by
    rw [← σ.prod_comp, Fin.prod_univ_three, P_eq_homfly, P_eq_homfly, P_eq_homfly, hA, hB, hC]
  have hMA : InSupportM 1 fA := by rw [← hA, ← P_eq_homfly]; exact P_knotRestrict_inSupportM_one J _
  have hMB : InSupportM 1 fB := by rw [← hB, ← P_eq_homfly]; exact P_knotRestrict_inSupportM_one J _
  have hMC : InSupportM 1 fC := by rw [← hC, ← P_eq_homfly]; exact P_knotRestrict_inSupportM_one J _
  have hsq : zRow 0 ((R.a - R.aInv) ^ 2 * (fA * fB * fC)) =
      (aPow 1 - aPow (-1)) ^ 2 * (zRow 0 fA * zRow 0 fB * zRow 0 fC) := by
    have e : (R.a - R.aInv) ^ 2 * (fA * fB * fC) =
        R.a * (R.a * (fA * fB * fC)) - R.a * (R.aInv * (fA * fB * fC)) -
          R.aInv * (R.a * (fA * fB * fC)) + R.aInv * (R.aInv * (fA * fB * fC)) := by ring
    rw [e]
    simp only [zRow_add, zRow_sub, zRow_a_mul, zRow_aInv_mul]
    rw [CV.zRow_zero_mul_of_inSupportM_one (hMA.one_mul_one hMB) hMC,
      CV.zRow_zero_mul_of_inSupportM_one hMA hMB]
    ring
  rw [← coeff_zRow, ← coeff_zRow, hsq, hlow, hprod, mul_assoc, coeff_T_mul']
  congr 1
  ring

/-- The move data of one configuration: the grouped contact diagrams `D_H`, `D_L` (cor:groupedknot (B)
on the two contact carriers), the double points `pxH, pyH` of `x, y` on the `K3` side and `pxL, pyL` on
the empty side, the linking number `Λ`, and the three outer grouped polynomials `f_A, f_B, f_C`.
Crossings of the diagrams are identified by their double points; smoothings are the library's
relational `IsOrientedSmoothing` (any smoothing site). -/
structure esc_MoveData (D_H D_L : Diagram) (pxH pyH pxL pyL : Plane) (Λ : ℕ) (fA fB fC : R) : Prop where
  /-- (4), for the crossings at the double points of `x`. -/
  switch_riii : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL → esc_switch_riii D_H D_L x_H x_L
  /-- (6), for every pair of oriented smoothings at `x` and the crossings at the double points of `y`. -/
  rii_after_smoothing : ∀ (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing),
    D_H.Γ.crossingPoint x_H = pxH → D_L.Γ.crossingPoint x_L = pxL →
    ∀ (D_H0 D_L0 : Diagram), IsOrientedSmoothing D_H x_H D_H0 → IsOrientedSmoothing D_L x_L D_L0 →
    ∀ (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing),
      D_H0.Γ.crossingPoint y_H = pyH → D_L0.Γ.crossingPoint y_L = pyL →
      esc_rii_after_smoothing D_H0 D_L0 y_H y_L
  /-- "Smoothing `x` in the `K3` word splits the contact knot into two components; there `y` is mixed,
  so smoothing `y` joins them and `D_H^{xy}` is a knot" (ESC §2). -/
  knot_after_two : ∀ (x_H : D_H.Γ.Crossing), D_H.Γ.crossingPoint x_H = pxH →
    ∀ D_H0 : Diagram, IsOrientedSmoothing D_H x_H D_H0 →
    ∀ (y_H : D_H0.Γ.Crossing), D_H0.Γ.crossingPoint y_H = pyH →
    ∀ J_H : Diagram, IsOrientedSmoothing D_H0 y_H J_H → J_H.componentCount = 1
  /-- (9)–(11) for the double smoothing `D_L^{xy}` ("`D_L^{xy}` has three components", ESC §2–§3): its
  three components are the grouped knots of the outer carriers, `Λ = lk(J)`. -/
  three_components : ∀ (x_L : D_L.Γ.Crossing), D_L.Γ.crossingPoint x_L = pxL →
    ∀ D_L0 : Diagram, IsOrientedSmoothing D_L x_L D_L0 →
    ∀ (y_L : D_L0.Γ.Crossing), D_L0.Γ.crossingPoint y_L = pyL →
    ∀ J_L : Diagram, IsOrientedSmoothing D_L0 y_L J_L → esc_three_components J_L Λ fA fB fC

/-- **The carrier split of the full row `Q ∪ T` on the empty side** (ESC §1, §4): the four
triangle-touching carriers — the three outer carriers `A, B, C` ("All nonlocal corners of the empty
contact carrier partition among the three outer carriers") and the central triangle `Z` — of the
support `Q ∪ T`, relative to the contact carrier `q₀` of the empty row `Q`; `Λ = lk(J)` of (12)/(17). -/
structure esc_FullSplitData (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P) (e f g : ZMod n)
    {Q : Finset (Crossing P)} (hQ : Q ∈ CV.Ind hG.crossingGeometry)
    (hS : Q ∪ triangleCrossings P e f g ∈ CV.Ind hG.crossingGeometry)
    (q₀ : GeoComponent hG.crossingGeometry Q)
    (A B C Z : GeoComponent hG.crossingGeometry (Q ∪ triangleCrossings P e f g)) (Λ : ℕ) : Prop where
  /-- the triangle-touching carriers of `Q ∪ T` are exactly `A, B, C, Z` -/
  touching_iff : ∀ q, ¬ TriangleDisjoint hG.crossingGeometry (Q ∪ triangleCrossings P e f g) e f g q ↔
    (q = A ∨ q = B ∨ q = C ∨ q = Z)
  distinct : A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z
  /-- "the central carrier's empty polynomial" (ESC §5): the central triangle carries no piece -/
  central_no_piece : CV.piecesOn hG.crossingGeometry (Q ∪ triangleCrossings P e f g) Z = ∅
  /-- "`lem:uniformrot(i)` gives it absolute rotation one" (ESC §4) -/
  central_rot : CV.carrierR hn hG hS Z = 1
  /-- (17) "`w = 3 + w_A + w_B + w_C + 2Λ`" -/
  writhe : CV.groupedWrithe hG q₀ =
    3 + CV.groupedWrithe hG A + CV.groupedWrithe hG B + CV.groupedWrithe hG C + 2 * (Λ : ℤ)
  /-- "If the empty contact carrier is mixed, then `W = 0`. The full selector is also zero" -/
  mixed : CV.CarrierMixed hG.crossingGeometry Q q₀ →
    CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
      CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0
  /-- "Each outer carrier is uniform in the live branch and exactly one-dissent in the dead branch …
  after a possible orientation reversal, `thm:carrierfloor` applies" (ESC §4) -/
  outer_alternative : CV.CarrierUniform hG.crossingGeometry Q q₀ →
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ A) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ B) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry _ C)
  /-- the two exhaustive branches of a uniform contact carrier: live `χ = 1` — (16) "`R_A+R_B+R_C = R+1`"
  and (14) "`W_full = -W`"; dead `χ = 0` — (16) "`R_A+R_B+R_C = R-1`" and "`W_full = 0`" -/
  uniform : CV.CarrierUniform hG.crossingGeometry Q q₀ →
    (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C = CV.carrierR hn hG hQ q₀ + 1 ∧
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z =
        -CV.weight hG.crossingGeometry Q q₀) ∨
    (CV.carrierR hn hG hS A + CV.carrierR hn hG hS B + CV.carrierR hn hG hS C + 1 = CV.carrierR hn hG hQ q₀ ∧
      CV.weight hG.crossingGeometry _ A * CV.weight hG.crossingGeometry _ B *
        CV.weight hG.crossingGeometry _ C * CV.weight hG.crossingGeometry _ Z = 0)

/-- **The interface of row 177** (never mapped): at every configuration of the row's `couple` field —
`t` the `K3` side, `t'` the empty side, `Q` an outside support at full availability, `q₀`/`q₀'` the
triangle-touching carriers of the empty row on the two sides — the carrier split of `Q ∪ T` on the empty
side and the move data of the two grouped contact diagrams exist with a common `Λ` and with the
outer grouped polynomials `f_A, f_B, f_C`. -/
def esc_interface : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (_hL : LocalizationData E e f g δ)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (_hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ (Q : Finset (Crossing (E.curve t))), Q ∈ outsideSupports (geomAt E t ht.1) e f g →
    FullAvail (geomAt E t ht.1) e f g Q →
    ∀ (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
      (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
      (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        esc_MoveData (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)

/-! #### E. The ledger -/

/-- **(7) and (13) in one step**: from the two skein equations at `x` and at `y` on each side, the two
move identities (4), (6), knot parity (8) and the three-component row (12),
"`Omega_H - Omega_L = -[a^(d+2+2Λ)] (a-a^(-1))^2 K(a)`" — for any positive crossings `x_H, x_L` of two
diagrams `D_H, D_L`, and any positive crossings `y_H, y_L` of oriented smoothings there. -/
theorem esc_coefficient_identity {D_H D_L D_H0 D_L0 J_H J_L : Diagram}
    {x_H : D_H.Γ.Crossing} {x_L : D_L.Γ.Crossing} {y_H : D_H0.Γ.Crossing} {y_L : D_L0.Γ.Crossing}
    (hxH : D_H.IsPositive x_H) (hxL : D_L.IsPositive x_L)
    (hsmH : IsOrientedSmoothing D_H x_H D_H0) (hsmL : IsOrientedSmoothing D_L x_L D_L0)
    (hyH : D_H0.IsPositive y_H) (hyL : D_L0.IsPositive y_L)
    (hsmJH : IsOrientedSmoothing D_H0 y_H J_H) (hsmJL : IsOrientedSmoothing D_L0 y_L J_L)
    (m4 : esc_switch_riii D_H D_L x_H x_L) (m6 : esc_rii_after_smoothing D_H0 D_L0 y_H y_L)
    (hJH : J_H.componentCount = 1) {Λ : ℕ} {K : R}
    (h12 : ∀ p : ℤ, coeffAt p (-2) (homfly J_L) = coeffAt (p + 2 * (Λ : ℤ)) 0 ((R.a - R.aInv) ^ 2 * K))
    (d : ℤ) :
    coeffAt d 0 (homfly D_H - homfly D_L) =
      -coeffAt (d + 2 + 2 * (Λ : ℤ)) 0 ((R.a - R.aInv) ^ 2 * K) := by
  have sk1 := CV.ax_homfly.skein D_H (D_H.switch x_H) D_H0 ⟨x_H, hxH, rfl, hsmH⟩
  have sk2 := CV.ax_homfly.skein D_L (D_L.switch x_L) D_L0 ⟨x_L, hxL, rfl, hsmL⟩
  have sk3 := CV.ax_homfly.skein D_H0 (D_H0.switch y_H) J_H ⟨y_H, hyH, rfl, hsmJH⟩
  have sk4 := CV.ax_homfly.skein D_L0 (D_L0.switch y_L) J_L ⟨y_L, hyL, rfl, hsmJL⟩
  unfold esc_switch_riii at m4
  unfold esc_rii_after_smoothing at m6
  have u := R.aInv_mul_a
  -- (7): `F_H − F_L = a^{−2} z^{2} (P(J_H) − P(J_L))`
  have h7 : homfly D_H - homfly D_L = single (-2, 2) 1 * (homfly J_H - homfly J_L) := by
    rw [← esc_aInv_aInv_z_z]
    linear_combination (R.aInv * R.aInv * R.z) * (sk3 - sk4) + R.aInv * (sk1 - sk2) +
      (R.aInv * R.aInv) * m4 + (R.aInv * R.aInv * R.aInv * R.z) * m6 -
      ((homfly D_H - homfly D_L) + R.aInv * R.z * (homfly D_H0 - homfly D_L0)) * u
  rw [h7, esc_coeffAt_single_mul, one_mul, coeffAt_sub, show d - -2 = d + 2 by ring,
    show (0 : ℤ) - 2 = -2 by norm_num, esc_knot_coeff_neg_two J_H hJH, zero_sub, h12]

/-- **The contact identity**: the difference of the two touching factors of the empty row is the
touching factor of the full row on the empty side (ESC §1–§5 at one configuration), from the interface
data and `CarrierSlotFloor`. -/
theorem esc_contact_identity (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n}
    {δ : ℝ} (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef₀ : e ≠ f) (heg₀ : e ≠ g) (hfg₀ : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (_hK : CompleteLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1))
    (hI : ∀ (q₀ : GeoComponent (geomAt E t ht.1) Q)
      (q₀' : GeoComponent (geomAt E t' ht'.1) (transportSupport hs Q)),
      ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q₀ →
      ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q₀' →
      ∃ (A B C Z : GeoComponent (geomAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)) (Λ : ℕ),
        esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ ∧
        esc_MoveData (CV.carrierDiagram hn (genericAt E t ht.1) hQi q₀)
          (CV.carrierDiagram hn (genericAt E t' ht'.1) hQi' q₀')
          (crossingPoint (xPair hef)) (crossingPoint (xPair heg))
          (crossingPoint (xPair ((hs _).mp hef))) (crossingPoint (xPair ((hs _).mp heg))) Λ
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' A) (CV.groupedPoly hn (genericAt E t' ht'.1) hS' B)
          (CV.groupedPoly hn (genericAt E t' ht'.1) hS' C)) :
    touchingFactor hn (genericAt E t ht.1) hQi e f g -
        touchingFactor hn (genericAt E t' ht'.1) hQi' e f g =
      touchingFactor hn (genericAt E t' ht'.1) hS' e f g := by
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  -- the contact carrier on the `K3` side
  obtain ⟨q₀, hq₀⟩ := esc_contact_exists ht hef Q
  have huniq : ∀ q, ¬ TriangleDisjoint (geomAt E t ht.1) Q e f g q ↔ q = q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht hQ hfull hq hq₀, fun h => h ▸ hq₀⟩
  have hTq₀ := esc_contact_owns hL hef₀ heg₀ hfg₀ ht hQ hfull hq₀
  -- the wall and the transported contact carrier on the empty side
  have W := GT_empty_wall hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q₀
  have hq₀' : ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g
      (GT_carrierEquiv W q₀) := by
    rw [esc_not_triangleDisjoint_iff]
    have hmem : crossingTransport hs (xPair hef) ∈
        geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs Q) (GT_carrierEquiv W q₀) := by
      rw [hX, Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact hTq₀ ((P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl))
    obtain ⟨i, -, -⟩ := crossing_visits_exist (crossingTransport hs (xPair hef))
    exact ⟨⟨_, i⟩, (P1.mem_triangleSupports _).mpr (Or.inl rfl),
      ((mem_geoCarrierCrossings _ _ _ _).mp hmem).2 _ rfl⟩
  have huniq' : ∀ q, ¬ TriangleDisjoint (geomAt E t' ht'.1) (transportSupport hs Q) e f g q ↔
      q = GT_carrierEquiv W q₀ :=
    fun q => ⟨fun hq => esc_contact_unique hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq hq₀', fun h => h ▸ hq₀'⟩
  have hT'q₀' := esc_contact_owns hL hef₀ heg₀ hfg₀ ht' hQ' hfull' hq₀'
  -- the interface data
  obtain ⟨A, B, C, Z, Λ, hsplit, hmove⟩ := hI q₀ (GT_carrierEquiv W q₀) hq₀ hq₀'
  -- notation
  set hG := genericAt E t ht.1
  set hG' := genericAt E t' ht'.1
  set q₀' := GT_carrierEquiv W q₀
  set D_H := CV.carrierDiagram hn hG hQi q₀
  set D_L := CV.carrierDiagram hn hG' hQi' q₀'
  set fA := CV.groupedPoly hn hG' hS' A
  set fB := CV.groupedPoly hn hG' hS' B
  set fC := CV.groupedPoly hn hG' hS' C
  -- the transported data of the contact carrier
  have hw : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = CV.weight hG.crossingGeometry Q q₀ :=
    GT_weight_eq hn hG hG' W q₀
  have hRq : CV.carrierR hn hG' hQi' q₀' = CV.carrierR hn hG hQi q₀ := GT_carrierR_eq hn hG hG' W hQi hQi' q₀
  have hwr : CV.groupedWrithe hG' q₀' = CV.groupedWrithe hG q₀ := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      hX, Finset.card_map]
  have hslot : CV.slot hn hG' hQi' q₀' = CV.slot hn hG hQi q₀ := by
    unfold CV.slot; rw [hRq, hwr]
  -- the two touching factors of the empty row and the one of the full row
  rw [esc_touchingFactor_eq_of_unique hn hG hQi e f g q₀ huniq,
    esc_touchingFactor_eq_of_unique hn hG' hQi' e f g q₀' huniq',
    esc_touchingFactor_eq_of_four hn hG' hS' e f g A B C Z hsplit.distinct hsplit.touching_iff, ← hw,
    ← mul_sub]
  -- the central carrier: `Ω₁ = 1`
  have hΩZ : CV.Omega1 hn hG' hS' Z = 1 := by
    unfold CV.Omega1 CV.slot
    rw [CV.groupedPoly_of_piecesOn_eq_empty hn hG' hS' Z hsplit.central_no_piece,
      CV.groupedWrithe_of_piecesOn_eq_empty hG' Z hsplit.central_no_piece, hsplit.central_rot]
    simp [coeffAt_one]
  rw [hΩZ]
  -- `Ω_H − Ω_L = [a^d z^0](F_H − F_L)`, `d` the common slot
  have hΩ : CV.Omega1 hn hG hQi q₀ - CV.Omega1 hn hG' hQi' q₀' =
      coeffAt (CV.slot hn hG' hQi' q₀') 0 (homfly D_H - homfly D_L) := by
    unfold CV.Omega1
    rw [hslot, GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly, coeffAt_sub]
  -- the crossings `x`, `y` on the grouped contact diagrams, the smoothings, the moves
  have hxT : xPair hef ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
  have hyT : xPair heg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hxT' : xPair hef' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inl rfl)
  have hyT' : xPair heg' ∈ triangleCrossings (E.curve t') e f g :=
    (P1.mem_triangleCrossings_iff hef' heg' hfg' _).mpr (Or.inr (Or.inl rfl))
  obtain ⟨x_H, hxH_pt, hxH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair hef) (hTq₀ hxT)
  obtain ⟨y_H, hyH_pt, hyH_pos⟩ := esc_lift_crossing hn hG hQi q₀ (xPair heg) (hTq₀ hyT)
  obtain ⟨x_L, hxL_pt, hxL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair hef') (hT'q₀' hxT')
  obtain ⟨y_L, hyL_pt, hyL_pos⟩ := esc_lift_crossing hn hG' hQi' q₀' (xPair heg') (hT'q₀' hyT')
  have hyxH : y_H ≠ x_H := by
    intro h
    apply P1.xPair_ef_ne_eg hef heg hfg
    apply crossingPoint_injective_of_geometry (geomAt E t ht.1)
    rw [← hxH_pt, ← hyH_pt, h]
  have hyxL : y_L ≠ x_L := by
    intro h
    apply P1.xPair_ef_ne_eg hef' heg' hfg'
    apply crossingPoint_injective_of_geometry (geomAt E t' ht'.1)
    rw [← hxL_pt, ← hyL_pt, h]
  obtain ⟨D_H0, hsmH, -⟩ := exists_smoothing_record_visit D_H x_H (D_H.overVisit x_H) rfl
  obtain ⟨D_L0, hsmL, -⟩ := exists_smoothing_record_visit D_L x_L (D_L.overVisit x_L) rfl
  obtain ⟨y_H0, hyH0_pt, hyH0_pos⟩ := esc_smoothing_outer hsmH y_H hyxH
  obtain ⟨y_L0, hyL0_pt, hyL0_pos⟩ := esc_smoothing_outer hsmL y_L hyxL
  rw [hyH_pt] at hyH0_pt
  rw [hyL_pt] at hyL0_pt
  obtain ⟨J_H, hsmJH, -⟩ := exists_smoothing_record_visit D_H0 y_H0 (D_H0.overVisit y_H0) rfl
  obtain ⟨J_L, hsmJL, -⟩ := exists_smoothing_record_visit D_L0 y_L0 (D_L0.overVisit y_L0) rfl
  have m4 := hmove.switch_riii x_H x_L hxH_pt hxL_pt
  have m6 := hmove.rii_after_smoothing x_H x_L hxH_pt hxL_pt D_H0 D_L0 hsmH hsmL y_H0 y_L0 hyH0_pt hyL0_pt
  have hJH := hmove.knot_after_two x_H hxH_pt D_H0 hsmH y_H0 hyH0_pt J_H hsmJH
  have h12 := esc_three_component_row (hmove.three_components x_L hxL_pt D_L0 hsmL y_L0 hyL0_pt J_L hsmJL)
  -- (13)
  have h13 := esc_coefficient_identity hxH_pos hxL_pos hsmH hsmL (hyH0_pos.mpr hyH_pos)
    (hyL0_pos.mpr hyL_pos) hsmJH hsmJL m4 m6 hJH h12 (CV.slot hn hG' hQi' q₀')
  rw [hΩ, h13, esc_coeffAt_sq_mul]
  -- the three selector branches on the empty contact carrier
  set d := CV.slot hn hG' hQi' q₀' with hd
  set K := fA * fB * fC with hK
  have hprod : (CV.weight hG'.crossingGeometry _ A * CV.Omega1 hn hG' hS' A) *
      (CV.weight hG'.crossingGeometry _ B * CV.Omega1 hn hG' hS' B) *
      (CV.weight hG'.crossingGeometry _ C * CV.Omega1 hn hG' hS' C) *
      (CV.weight hG'.crossingGeometry _ Z * 1) =
      (CV.weight hG'.crossingGeometry _ A * CV.weight hG'.crossingGeometry _ B *
        CV.weight hG'.crossingGeometry _ C * CV.weight hG'.crossingGeometry _ Z) *
      (CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C) := by ring
  rw [hprod]
  by_cases huni : CV.CarrierUniform hG'.crossingGeometry (transportSupport hs Q) q₀'
  · -- the uniform contact carrier: the outer floors
    obtain ⟨haltA, haltB, haltC⟩ := hsplit.outer_alternative huni
    have hqA := esc_quadrant_groupedPoly hF hn hG' hS' A haltA
    have hqB := esc_quadrant_groupedPoly hF hn hG' hS' B haltB
    have hqC := esc_quadrant_groupedPoly hF hn hG' hS' C haltC
    have hqK := esc_quadrant_mul (esc_quadrant_mul hqA hqB) hqC
    -- (19)
    have h19 : coeffAt (CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C) 0 K =
        CV.Omega1 hn hG' hS' A * CV.Omega1 hn hG' hS' B * CV.Omega1 hn hG' hS' C := by
      rw [hK, esc_coeffAt_corner (esc_quadrant_mul hqA hqB) hqC, esc_coeffAt_corner hqA hqB]
      rfl
    have hwrq := hsplit.writhe
    have hdq : d = 1 - CV.groupedWrithe hG' q₀' - (CV.carrierR hn hG' hQi' q₀' : ℤ) := rfl
    rcases hsplit.uniform huni with ⟨hrot, hwf⟩ | ⟨hrot, hwf⟩
    · -- live branch `χ = 1`: (18) `D = d + 4 + 2Λ`; (20) `Ω_H − Ω_L = −ω_A ω_B ω_C`
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C =
          CV.carrierR hn hG' hQi' q₀' + 1 := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 4 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at h19 hqK
      rw [show d + 2 + 2 * (Λ : ℤ) - 2 = d + 2 * Λ by ring,
        show d + 2 + 2 * (Λ : ℤ) + 2 = d + 4 + 2 * Λ by ring, h19,
        hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega), hwf]
      ring
    · -- dead branch `χ = 0`: (18) `D = d + 6 + 2Λ`; every sample is below the floor
      have hrot' : (CV.carrierR hn hG' hS' A : ℤ) + CV.carrierR hn hG' hS' B + CV.carrierR hn hG' hS' C + 1 =
          CV.carrierR hn hG' hQi' q₀' := by exact_mod_cast hrot
      have hD : CV.slot hn hG' hS' A + CV.slot hn hG' hS' B + CV.slot hn hG' hS' C = d + 6 + 2 * (Λ : ℤ) := by
        simp only [CV.slot] at hdq ⊢
        omega
      rw [hD] at hqK
      rw [hqK.coeffAt_eq_zero (by omega), hqK.coeffAt_eq_zero (by omega),
        hqK.coeffAt_eq_zero (by omega), hwf]
      ring
  · -- the mixed contact carrier: `W = 0` and `W_full = 0`
    have hW0 : CV.weight hG'.crossingGeometry (transportSupport hs Q) q₀' = 0 :=
      CV.weight_of_mixed _ _ q₀' huni
    rw [hsplit.mixed huni, hW0]
    ring

/-- **The `couple` field of row 177** from the interface, `CarrierSlotFloor`, and the accepted data at a
common radius: (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`" — the exterior factor `C_Q` is common to the
three rows (row 168: `EXT_exteriorFactor_wall`, `EXT_exteriorFactor_eq_base`), the rest is the contact
identity.  "No exterior scalar, selector, or coefficient was divided out." -/
theorem esc_couple (hI : esc_interface) (hF : CV.CarrierSlotFloor) (hn : 3 ≤ n) {E : CV.Event n}
    {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q - rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) =
        rowTerm hn (genericAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g) := by
  intro t t' ht ht' hop hs hef heg hfg hK Q hQ hfull
  have hef₀ : e ≠ f := AV_ne_of_remote h3.1
  have hfg₀ : f ≠ g := AV_ne_of_remote h3.2.1
  have heg₀ : e ≠ g := AV_ne_of_remote h3.2.2.1
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) := mem_Ind_of_mem_outsideSupports hQ'
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hEmpty : EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg' :=
    (PRE_176_graphs_complementary hL t t' ht ht' hop hef heg hfg hef' heg' hfg').mp hK
  have hS' : transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g ∈ CV.Ind (geomAt E t' ht'.1) :=
    PRE_177_full_present_on_empty E e f g δ t' ht' hef' heg' hfg' hEmpty _ hQ' hfull'
  -- the exterior factor `C_Q` of the three rows (row 168)
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hx hxT =>
    Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hQT y hy
  rw [rowTerm_eq_exterior_mul_touching hn (genericAt E t ht.1) hQi e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hQi' e f g,
    rowTerm_eq_exterior_mul_touching hn (genericAt E t' ht'.1) hS' e f g,
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi',
    ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
      (fun x hx => (P1.mem_triangleCrossings x).mp hx) hS' hQi',
    EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQi hQT hQi', ← mul_sub]
  congr 1
  exact esc_contact_identity hF hn hL hR hef₀ heg₀ hfg₀ ht ht' hop hs hef heg hfg hK hQ hfull hQi hQi' hS'
    (fun q₀ q₀' hq₀ hq₀' => hI hn E e f g δ hL t t' ht ht' hop hs hef heg hfg hK Q hQ hfull hQi hQi' hS'
      q₀ q₀' hq₀ hq₀')

/-- **The RA ledger of row 177** (D-F11): the fixed row shape from the interface and `CarrierSlotFloor`;
the two presupposition fields are the accepted `PRE_177_*`, the radius is the minimum of the accepted
radii of rows 164 (`localization`), the sign data (`AV_exists_eventRadius`) and the guard
(`EXT_exists_guardRadius`). -/
theorem esc_ledger (hI : esc_interface) (hF : CV.CarrierSlotFloor) : RowShape @ExtremeSelectedData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  obtain ⟨δG, hδG, -, hguard⟩ := EXT_exists_guardRadius hE
  refine ⟨min δL (min δR δG), lt_min hδL (lt_min hδR hδG), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δR δG)) hL
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δR δG)).trans (min_le_left δR δG)) hR
  have hguard' : ∀ u : E.Parameter, |u.val| < min δL (min δR δG) → EXT_GuardAt E u :=
    fun u hu => hguard u (lt_of_lt_of_le hu ((min_le_right _ _).trans (min_le_right _ _)))
  exact { full_present_on_empty := PRE_177_full_present_on_empty E e f g _
          full_absent_on_complete := PRE_177_full_absent_on_complete E e f g _
          couple := esc_couple hI hF hn hE hL' hR' hguard' }

end ESC

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
  exact esc_ledger (by sorry) (CV.carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) n hn E e f g h3 h4e h4f h4g hE

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
