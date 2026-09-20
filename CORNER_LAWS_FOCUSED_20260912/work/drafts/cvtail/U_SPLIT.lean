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

/-! ### U-SPLIT helpers (prefix `cvt165s_`): the singleton split on the geo layer.

Route (PLAN_FINAL §4, U-SPLIT (a)–(e); template: the corner lane's U103-B/E units on SM's `Component`,
ported here to `GeoComponent`/`piecesOn`/`groupedPoly`):
(a) `insert c S ∈ Ind` (`geoIndependent_insert_unselected`), `U(insert c S) = U(S) ∖ {c}` membership-wise, and
    `Piece (insert c S) ≃ {H : Piece S // pieceLabels H ≠ {c}}` label-preserving (Mathlib `induceHomOfLE`;
    `c` is isolated in `G_P[U(S)]` because its piece is `{c}`);
(b) the carrier split: `Λ₁ = geoOwner (insert c S) (inr v)`, `Λ₂ = geoOwner (insert c S) (inr (visitTwin v))` for a
    visit `v` of `c` (`geoComponentForgetSwitch_fiber_affected`, `geoOwner_insert_eq_imp`,
    `geo_selected_visits_separated`);
(c) `piecesOn S A = insert (pieceOf c) ((piecesOn S' Λ₁ ∪ piecesOn S' Λ₂).map emb)`; `pieceHomfly` is a function
    of the labels (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`, lem:pieceintrinsic) and
    `pieceHomfly (pieceOf c) = 1` (lc:single-crossing), `pieceWrithe (pieceOf c) = 1`;
(d) rotation: the real principal turn of a corner is a function of its corner MARK
    (`geoCornerPolygon_edge_smul/_edge_pred_smul` + `principalAngle_smul`), `2π rot = Σ` over the corner-mark
    finset, inherited corners keep their turn, the two smoothing corners cancel (`principalAngle_swap`); the
    signs put all three integers on one ray (lem:uniformrot);
(e) the sign pattern of each daughter (uniform with `A`'s sign or one dissent) gives `UniformOrOneDissentCV`
    in the literal reversal form (`principalTurn_reversal`). -/

/-! (e), polygon side: signed turn patterns, the rays of lem:uniformrot, and the literal reversal form. -/

section Cvt165sPattern

/-- Two nonzero signs agree or are opposite. -/
theorem cvt165s_signType_eq_or_neg {σ τ : SignType} (hσ : σ ≠ 0) (hτ : τ ≠ 0) : σ = τ ∨ σ = -τ := by
  revert hσ hτ
  revert σ τ
  decide

variable {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L)

include hL in
theorem cvt165s_sign_principalTurn (k : ZMod c) : SignType.sign (principalTurn L k) = turn L k := by
  rw [principalTurn_eq_sm]
  exact SM.principalTurn_sign ((regular_iff_sm L).mp hL) k

omit [NeZero c] in
include hL in
theorem cvt165s_principalTurn_reversal (k : ZMod c) :
    principalTurn (reversal L) k = -principalTurn L (2 - k) := by
  rw [principalTurn_eq_sm, principalTurn_eq_sm]
  exact SM.principalTurn_reversal ((regular_iff_sm L).mp hL) k

include hL in
/-- lem:uniformrot read at a signed pattern: a regular polygon that is uniform of sign `τ` or has exactly
one dissent `−τ` has its rotation on the ray of `τ` (`one_le_rot_of_pos`, `one_le_rot_of_one_dissent`,
and their reversal forms). -/
theorem cvt165s_rot_ray (τ : SignType)
    (h : (∀ k, turn L k = τ) ∨ (∃ k₀, turn L k₀ = -τ ∧ ∀ k, k ≠ k₀ → turn L k = τ)) :
    (τ = 1 → 1 ≤ rot L hL) ∧ (τ = -1 → rot L hL ≤ -1) := by
  have hsign := cvt165s_sign_principalTurn L hL
  constructor
  · rintro rfl
    rcases h with h | ⟨k₀, -, hoth⟩
    · exact one_le_rot_of_pos hL fun k => sign_eq_one_iff.mp ((hsign k).trans (h k))
    · exact one_le_rot_of_one_dissent hL k₀ fun k hk =>
        (sign_eq_one_iff.mp ((hsign k).trans (hoth k hk))).le
  · rintro rfl
    have hrev : Regular (reversal L) := regular_reversal' hL
    have hrevturn := cvt165s_principalTurn_reversal L hL
    have key : 1 ≤ rot (reversal L) hrev := by
      rcases h with h | ⟨k₀, -, hoth⟩
      · refine one_le_rot_of_pos hrev fun k => ?_
        rw [hrevturn]
        have := sign_eq_neg_one_iff.mp ((hsign (2 - k)).trans (h (2 - k)))
        linarith
      · refine one_le_rot_of_one_dissent hrev (2 - k₀) fun k hk => ?_
        rw [hrevturn]
        have hne : 2 - k ≠ k₀ := fun he => hk (by rw [← he, sub_sub_cancel])
        have := sign_eq_neg_one_iff.mp ((hsign (2 - k)).trans (hoth (2 - k) hne))
        linarith
    rw [rot_reversal hL hrev] at key
    omega

include hL in
/-- (e) A signed pattern gives the literal reversal form `UniformOrOneDissentCV`. -/
theorem cvt165s_uniformOrOneDissent_of_pattern (τ : SignType) (hτ0 : τ ≠ 0)
    (h : (∀ k, turn L k = τ) ∨ (∃ k₀, turn L k₀ = -τ ∧ ∀ k, k ≠ k₀ → turn L k = τ)) :
    UniformOrOneDissentCV L := by
  have hsign := cvt165s_sign_principalTurn L hL
  have hrevturn := cvt165s_principalTurn_reversal L hL
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · right
    rcases h with h | ⟨k₀, hk₀, hoth⟩
    · left
      intro k
      rw [hrevturn]
      have := sign_eq_neg_one_iff.mp ((hsign (2 - k)).trans (h (2 - k)))
      linarith
    · right
      refine ⟨2 - k₀, ?_, fun j hj => ?_⟩
      · rw [hrevturn, sub_sub_cancel]
        have h1 : turn L k₀ = 1 := by
          rw [hk₀]
          decide
        have := sign_eq_one_iff.mp ((hsign k₀).trans h1)
        linarith
      · rw [hrevturn]
        have hne : 2 - j ≠ k₀ := fun he => hj (by rw [← he, sub_sub_cancel])
        have := sign_eq_neg_one_iff.mp ((hsign (2 - j)).trans (hoth (2 - j) hne))
        linarith
  · exact absurd rfl hτ0
  · left
    rcases h with h | ⟨k₀, hk₀, hoth⟩
    · left
      exact fun k => sign_eq_one_iff.mp ((hsign k).trans (h k))
    · right
      exact ⟨k₀, sign_eq_neg_one_iff.mp ((hsign k₀).trans hk₀),
        fun j hj => sign_eq_one_iff.mp ((hsign j).trans (hoth j hj))⟩


/-- Two integers on one ray have additive absolute values (the `ω`-free arithmetic of (d), kept outside the
classical-instance region so that `omega` may be used). -/
theorem cvt165s_abs_add_of_ray (a b : ℤ) :
    (a ≤ -1 → b ≤ -1 → |a + b| = |a| + |b|) ∧ (1 ≤ a → 1 ≤ b → |a + b| = |a| + |b|) := by
  constructor
  · intro ha hb
    rw [abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega)]
    ring
  · intro ha hb
    rw [abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega)]

end Cvt165sPattern

section Cvt165s

/- The library states everything about `insert`, `∪`, `filter` on `Crossing P` with the classical
`DecidableEq` (every CV/SM module has `attribute [local instance high] Classical.propDecidable`); the frozen
statements of this file elaborate `insert c S` with the global `RProof.instDecidableEqCrossing`. The helpers
below follow the library; the leaf bridges the two through `cvt165s_insert_eq` (a `Subsingleton` fact). -/
attribute [local instance high] Classical.propDecidable

/-- `insert` does not depend on the `DecidableEq` instance (bridge between the frozen statement's instance
and the library's classical one). -/
theorem cvt165s_insert_eq {α : Type*} [inst : DecidableEq α] (a : α) (s : Finset α) :
    @insert α (Finset α) (@Finset.instInsert α inst) a s =
      @insert α (Finset α) (@Finset.instInsert α fun x y => Classical.propDecidable (x = y)) a s :=
  congrArg (fun i : DecidableEq α => @insert α (Finset α) (@Finset.instInsert α i) a s)
    (Subsingleton.elim _ _)

section Cvt165sGraph

variable {V : Type*} (G : SimpleGraph V) {s t : Set V} {c : V}

/-- An isolated vertex of `G[s]` reaches no other vertex of `G[s]`. -/
theorem cvt165s_not_reachable_of_isolated (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    {z : s} (hz : z.1 ≠ c) : ¬ (G.induce s).Reachable ⟨c, hcs⟩ z := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hz rfl
  | cons h _ => exact hc _ (Subtype.mem _) h.symm

/-- A walk of `G[s]` between vertices other than the isolated `c` never visits `c`: reachability descends
to `G[t]`, `t = s ∖ {c}` (given membership-wise). -/
theorem cvt165s_reachable_descend (hc : ∀ x ∈ s, ¬ G.Adj x c) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c)
    {x y : s} (hx : x.1 ≠ c) (hy : y.1 ≠ c) (h : (G.induce s).Reachable x y) :
    (G.induce t).Reachable ⟨x.1, (ht _).mpr ⟨x.2, hx⟩⟩ ⟨y.1, (ht _).mpr ⟨y.2, hy⟩⟩ := by
  obtain ⟨p⟩ := h
  revert hx hy
  induction p with
  | nil => intro _ _; exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
    intro hu hw
    have hv : v.1 ≠ c := by
      intro hvc
      have h' : G.Adj u.1 v.1 := huv
      rw [hvc] at h'
      exact hc _ u.2 h'
    exact (SimpleGraph.Adj.reachable
      (show (G.induce t).Adj ⟨u.1, (ht _).mpr ⟨u.2, hu⟩⟩ ⟨v.1, (ht _).mpr ⟨v.2, hv⟩⟩ from huv)).trans
      (ih hv hw)

/-- The inclusion `G[t] ↪ G[s]` on connected components. -/
def cvt165s_compMap (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    (G.induce t).ConnectedComponent → (G.induce s).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (G.induceHomOfLE fun x hx => ((ht x).mp hx).1).toHom

theorem cvt165s_compMap_mk (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (x : t) :
    cvt165s_compMap G ht ((G.induce t).connectedComponentMk x) =
      (G.induce s).connectedComponentMk ⟨x.1, ((ht x).mp x.2).1⟩ := rfl

theorem cvt165s_compMap_injective (hc : ∀ x ∈ s, ¬ G.Adj x c) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    Function.Injective (cvt165s_compMap G ht) := by
  intro C D
  refine SimpleGraph.ConnectedComponent.ind₂ (fun x y h => ?_) C D
  rw [cvt165s_compMap_mk, cvt165s_compMap_mk, SimpleGraph.ConnectedComponent.eq] at h
  exact SimpleGraph.ConnectedComponent.sound
    (cvt165s_reachable_descend G hc ht ((ht _).mp x.2).2 ((ht _).mp y.2).2 h)

theorem cvt165s_mem_range_compMap_iff (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (C : (G.induce s).ConnectedComponent) :
    C ∈ Set.range (cvt165s_compMap G ht) ↔ C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩ := by
  refine SimpleGraph.ConnectedComponent.ind (fun x => ?_) C
  constructor
  · rintro ⟨D, hD⟩ hx
    refine SimpleGraph.ConnectedComponent.ind (fun z hD => ?_) D hD
    rw [cvt165s_compMap_mk, hx, SimpleGraph.ConnectedComponent.eq] at hD
    exact cvt165s_not_reachable_of_isolated G hc hcs ((ht _).mp z.2).2 hD.symm
  · intro hx
    have hxc : x.1 ≠ c := fun h => hx (congrArg _ (Subtype.ext h))
    exact ⟨(G.induce t).connectedComponentMk ⟨x.1, (ht _).mpr ⟨x.2, hxc⟩⟩, rfl⟩

/-- **The components of `G[s ∖ {c}]` are the components of `G[s]` other than that of the isolated `c`.** -/
def cvt165s_compEquiv (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s) (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) :
    (G.induce t).ConnectedComponent ≃
      {C : (G.induce s).ConnectedComponent // C ≠ (G.induce s).connectedComponentMk ⟨c, hcs⟩} :=
  (Equiv.ofInjective _ (cvt165s_compMap_injective G hc ht)).trans
    (Equiv.subtypeEquivRight (cvt165s_mem_range_compMap_iff G hc hcs ht))

theorem cvt165s_compEquiv_apply_val (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (D : (G.induce t).ConnectedComponent) :
    (cvt165s_compEquiv G hc hcs ht D).1 = cvt165s_compMap G ht D := rfl

/-- Vertex by vertex: `x` lies in the component `e D` of `G[s]` iff it lies in `D`. -/
theorem cvt165s_compEquiv_mem_iff (hc : ∀ x ∈ s, ¬ G.Adj x c) (hcs : c ∈ s)
    (ht : ∀ x, x ∈ t ↔ x ∈ s ∧ x ≠ c) (D : (G.induce t).ConnectedComponent) (x : V) :
    (∃ hx : x ∈ s, (G.induce s).connectedComponentMk ⟨x, hx⟩ = (cvt165s_compEquiv G hc hcs ht D).1) ↔
      ∃ hx : x ∈ t, (G.induce t).connectedComponentMk ⟨x, hx⟩ = D := by
  refine SimpleGraph.ConnectedComponent.ind (fun z => ?_) D
  rw [cvt165s_compEquiv_apply_val, cvt165s_compMap_mk]
  constructor
  · rintro ⟨hx, h⟩
    rw [SimpleGraph.ConnectedComponent.eq] at h
    have hxc : x ≠ c := by
      intro hxc
      have hxe : (⟨x, hx⟩ : s) = ⟨c, hcs⟩ := Subtype.ext hxc
      rw [hxe] at h
      exact cvt165s_not_reachable_of_isolated G hc hcs ((ht _).mp z.2).2 h
    exact ⟨(ht x).mpr ⟨hx, hxc⟩, SimpleGraph.ConnectedComponent.sound
      (cvt165s_reachable_descend G hc ht hxc ((ht _).mp z.2).2 h)⟩
  · rintro ⟨hx, h⟩
    refine ⟨((ht x).mp hx).1, ?_⟩
    have := congrArg (cvt165s_compMap G ht) h
    rw [cvt165s_compMap_mk, cvt165s_compMap_mk] at this
    exact this

end Cvt165sGraph

/-! (a) The pieces of `insert c S` when the piece of `c` is `{c}`: `c` is isolated in `G_P[U(S)]`, and
`U(insert c S) = U(S) ∖ {c}`. -/

section Cvt165sPieces

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}
  {c : Crossing P}

/-- The piece of `c` is `{c}` ⇒ no undominated crossing interlaces `c` (an interlacing undominated
crossing would lie in the piece of `c`). -/
theorem cvt165s_not_interlaces (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c := by
  intro x hx hI
  have hadj : (residualGraph hP S).Adj ⟨x, hx⟩ ⟨c, hcU⟩ := hI
  have hH : pieceOf hP S x hx = pieceOf hP S c hcU :=
    SimpleGraph.ConnectedComponent.sound hadj.reachable
  have hxc : x ∈ pieceLabels hP S (pieceOf hP S c hcU) := (mem_pieceLabels hP S _ x).mpr ⟨hx, hH⟩
  rw [hlab, Finset.mem_singleton] at hxc
  subst hxc
  exact geometricInterlaces_irrefl hP x hI

/-- `U(insert c S) = U(S) ∖ {c}`, membership-wise. -/
theorem cvt165s_mem_U_insert_iff (hiso : ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c) (x : Crossing P) :
    x ∈ U hP (insert c S) ↔ x ∈ U hP S ∧ x ≠ c := by
  rw [mem_U_iff, mem_U_iff]
  constructor
  · rintro ⟨hxS', hxI⟩
    refine ⟨⟨fun h => hxS' (Finset.mem_insert_of_mem h), fun y hy => hxI y (Finset.mem_insert_of_mem hy)⟩,
      fun hxc => hxS' (hxc ▸ Finset.mem_insert_self c S)⟩
  · rintro ⟨⟨hxS, hxI⟩, hxc⟩
    refine ⟨fun h => ?_, fun y hy => ?_⟩
    · rcases Finset.mem_insert.mp h with h | h
      · exact hxc h
      · exact hxS h
    · rcases Finset.mem_insert.mp hy with h | hy
      · rw [h]
        exact hiso x ((mem_U_iff hP S x).mpr ⟨hxS, hxI⟩)
      · exact hxI y hy

theorem cvt165s_mem_U_set (hcU : c ∈ U hP S) : c ∈ (↑(U hP S) : Set (Crossing P)) :=
  Finset.mem_coe.mpr hcU

theorem cvt165s_mem_U_insert_iff_set (hiso : ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c) (x : Crossing P) :
    x ∈ (↑(U hP (insert c S)) : Set (Crossing P)) ↔ x ∈ (↑(U hP S) : Set (Crossing P)) ∧ x ≠ c := by
  rw [Finset.mem_coe, Finset.mem_coe]
  exact cvt165s_mem_U_insert_iff hP hiso x

theorem cvt165s_adj_isolated (hiso : ∀ x ∈ U hP S, ¬ GeometricInterlaces hP x c) :
    ∀ x ∈ (↑(U hP S) : Set (Crossing P)), ¬ (geometricInterlacementGraph hP).Adj x c :=
  fun x hx => hiso x (Finset.mem_coe.mp hx)

/-- A piece has the labels `{c}` iff it is the piece of `c`. -/
theorem cvt165s_pieceLabels_eq_singleton_iff (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H : Piece hP S) :
    pieceLabels hP S H = {c} ↔ H = pieceOf hP S c hcU := by
  constructor
  · intro h
    have hcH : c ∈ pieceLabels hP S H := by
      rw [h]
      exact Finset.mem_singleton_self c
    obtain ⟨_, hH⟩ := (mem_pieceLabels hP S H c).mp hcH
    exact hH.symm
  · rintro rfl
    exact hlab

/-- **`Piece (insert c S) ≃ {H : Piece S // pieceLabels H ≠ {c}}`**, label-preserving
(`cvt165s_pieceEquiv_labels`). -/
def cvt165s_pieceEquiv (hcU : c ∈ U hP S) (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    Piece hP (insert c S) ≃ {H : Piece hP S // pieceLabels hP S H ≠ {c}} :=
  (cvt165s_compEquiv (geometricInterlacementGraph hP)
      (cvt165s_adj_isolated hP (cvt165s_not_interlaces hP hcU hlab)) (cvt165s_mem_U_set hP hcU)
      (cvt165s_mem_U_insert_iff_set hP (cvt165s_not_interlaces hP hcU hlab))).trans
    (Equiv.subtypeEquivRight fun H =>
      (not_congr (cvt165s_pieceLabels_eq_singleton_iff hP hcU hlab H)).symm)

/-- **Label-preserving**: the labels of `e H'` (as a piece of `S`) are the labels of `H'` (as a piece of
`insert c S`). -/
theorem cvt165s_pieceEquiv_labels (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    pieceLabels hP S (cvt165s_pieceEquiv hP hcU hlab H').1 = pieceLabels hP (insert c S) H' := by
  ext x
  rw [mem_pieceLabels, mem_pieceLabels]
  exact cvt165s_compEquiv_mem_iff (geometricInterlacementGraph hP)
    (cvt165s_adj_isolated hP (cvt165s_not_interlaces hP hcU hlab)) (cvt165s_mem_U_set hP hcU)
    (cvt165s_mem_U_insert_iff_set hP (cvt165s_not_interlaces hP hcU hlab)) H' x

/-- The pieces of `insert c S` as pieces of `S`. -/
def cvt165s_pieceEmbedding (hcU : c ∈ U hP S) (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    Piece hP (insert c S) ↪ Piece hP S :=
  (cvt165s_pieceEquiv hP hcU hlab).toEmbedding.trans (Function.Embedding.subtype _)

theorem cvt165s_pieceEmbedding_apply (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    cvt165s_pieceEmbedding hP hcU hlab H' = (cvt165s_pieceEquiv hP hcU hlab H').1 := rfl

theorem cvt165s_pieceLabels_pieceEmbedding (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    pieceLabels hP S (cvt165s_pieceEmbedding hP hcU hlab H') = pieceLabels hP (insert c S) H' :=
  cvt165s_pieceEquiv_labels hP hcU hlab H'

/-- A piece of `S` is in the range of the embedding iff it is not the piece `{c}`. -/
theorem cvt165s_mem_range_pieceEmbedding_iff (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H : Piece hP S) :
    (∃ H', cvt165s_pieceEmbedding hP hcU hlab H' = H) ↔ pieceLabels hP S H ≠ {c} := by
  constructor
  · rintro ⟨H', rfl⟩
    exact (cvt165s_pieceEquiv hP hcU hlab H').2
  · intro h
    exact ⟨(cvt165s_pieceEquiv hP hcU hlab).symm ⟨H, h⟩, by
      rw [cvt165s_pieceEmbedding_apply, Equiv.apply_symm_apply]⟩

theorem cvt165s_pieceOf_notMem_map (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (T : Finset (Piece hP (insert c S))) :
    pieceOf hP S c hcU ∉ T.map (cvt165s_pieceEmbedding hP hcU hlab) := by
  rw [Finset.mem_map]
  rintro ⟨H', -, hH'⟩
  exact (cvt165s_pieceEquiv hP hcU hlab H').2
    ((cvt165s_pieceLabels_eq_singleton_iff hP hcU hlab _).mpr hH')

/-- `w(H)` is carried by the embedding (the labels are literally the same). -/
theorem cvt165s_pieceWrithe_pieceEmbedding (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) (H' : Piece hP (insert c S)) :
    pieceWrithe hP S (cvt165s_pieceEmbedding hP hcU hlab H') = pieceWrithe hP (insert c S) H' := by
  unfold pieceWrithe
  rw [cvt165s_pieceLabels_pieceEmbedding]

/-- `w({c}) = 1`. -/
theorem cvt165s_pieceWrithe_singleton (hcU : c ∈ U hP S)
    (hlab : pieceLabels hP S (pieceOf hP S c hcU) = {c}) :
    pieceWrithe hP S (pieceOf hP S c hcU) = 1 := by
  simp [pieceWrithe, hlab]

end Cvt165sPieces

/-! (b) The carrier split: for a visit `v` of `c`, the two daughters are the carriers of `v` and of
`visitTwin v` at `insert c S`; every mark of `A` lies on exactly one of them and no other mark does. -/

section Cvt165sOwner

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}
  {q : GeoComponent hP S} {v : Visit P} (hc : SingletonPieceOn hP S q v.1)

include hc in
theorem cvt165s_notMem : v.1 ∉ S := ((mem_U_iff hP S v.1).mp hc.mem_U).1

include hc in
/-- Both visits of `c` lie on `A` (the piece `{c}` is assigned to `A`). -/
theorem cvt165s_owner_visit (w : Visit P) (hw : w.1 = v.1) : geoOwner hP S (Sum.inr w) = q := by
  have h := (mem_piecesOn hP S q _).mp hc.owner
  refine h v.1 ?_ w hw
  rw [hc.labels]
  exact Finset.mem_singleton_self _

include hc in
theorem cvt165s_owner_eq_twin :
    geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr (visitTwin v)) := by
  rw [cvt165s_owner_visit hP hc v rfl, cvt165s_owner_visit hP hc (visitTwin v) (visitTwin_crossing v)]

include hc in
theorem cvt165s_sameCycle :
    (geoSmoothingSuccessor hP S).SameCycle (Sum.inr v) (Sum.inr (visitTwin v)) :=
  (geoOwner_eq_iff hP S _ _).mp (cvt165s_owner_eq_twin hP hc)

include hc in
/-- (a) `insert c S ∈ Ind(G_P)`: `c ∈ U(S)` interlaces no element of `S`. -/
theorem cvt165s_geoIndependent_insert (hS : S ∈ Ind hP) : GeoIndependent hP (insert v.1 S) :=
  geoIndependent_insert_unselected hP (geoIndependent_of_mem_Ind hP hS)
    (mem_geoSupportUnselected_of_mem_U hP hc.mem_U)

include hc in
theorem cvt165s_mem_Ind_insert (hS : S ∈ Ind hP) : insert v.1 S ∈ Ind hP :=
  (mem_Ind_iff_geoIndependent hP _).mpr (cvt165s_geoIndependent_insert hP hc hS)

include hc in
/-- The two daughters are distinct (conv:selected-visits separates the two visits of the selected `c`). -/
theorem cvt165s_daughters_ne (hS : S ∈ Ind hP) :
    geoOwner hP (insert v.1 S) (Sum.inr v) ≠ geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)) :=
  geo_selected_visits_separated hP (cvt165s_geoIndependent_insert hP hc hS) v (Finset.mem_insert_self _ _)

include hc in
/-- A mark of a daughter is a mark of `A` (the reconnection refines the carriers). -/
theorem cvt165s_owner_of_insert {m : Mark P}
    (h : geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr v) ∨
      geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v))) :
    geoOwner hP S m = q := by
  rcases h with h | h
  · rw [geoOwner_insert_eq_imp hP S v (cvt165s_notMem hP hc) (cvt165s_sameCycle hP hc) h]
    exact cvt165s_owner_visit hP hc v rfl
  · rw [geoOwner_insert_eq_imp hP S v (cvt165s_notMem hP hc) (cvt165s_sameCycle hP hc) h]
    exact cvt165s_owner_visit hP hc (visitTwin v) (visitTwin_crossing v)

include hc in
/-- A mark of `A` lies on one of the two daughters (the fibre of the forget map over `A` is exactly
the two daughters). -/
theorem cvt165s_owner_insert_of (hS : S ∈ Ind hP) {m : Mark P} (hm : geoOwner hP S m = q) :
    geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr v) ∨
      geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)) := by
  obtain ⟨-, hfib⟩ := geoComponentForgetSwitch_fiber_affected hP S
    (geoInheritsMarkOrder_of_independent hP (geoIndependent_of_mem_Ind hP hS)) v
    (cvt165s_notMem hP hc) (cvt165s_owner_eq_twin hP hc)
  rw [Finset.ext_iff] at hfib
  have hmem := (hfib (geoOwner hP (insert v.1 S) m)).mp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [geoComponentForgetSwitch_owner, hm, cvt165s_owner_visit hP hc v rfl]⟩)
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

include hc in
/-- **The marks of `A` are exactly the marks of the two daughters.** -/
theorem cvt165s_owner_iff (hS : S ∈ Ind hP) (m : Mark P) :
    geoOwner hP S m = q ↔
      geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr v) ∨
        geoOwner hP (insert v.1 S) m = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)) :=
  ⟨cvt165s_owner_insert_of hP hc hS, cvt165s_owner_of_insert hP hc⟩

end Cvt165sOwner

/-! (c) The pieces carried by the daughters, and the factorisation of `P_{S,A}` and `w_{S,A}`. -/

section Cvt165sProducts

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) {S : Finset (Crossing P)}

/-- Distinct carriers carry disjoint sets of pieces (lem:carriers (iv)). -/
theorem cvt165s_piecesOn_disjoint (hS : S ∈ Ind hP) {q r : GeoComponent hP S} (hqr : q ≠ r) :
    Disjoint (piecesOn hP S q) (piecesOn hP S r) := by
  rw [Finset.disjoint_left]
  intro H h1 h2
  rw [mem_piecesOn_iff hP hS] at h1 h2
  exact hqr (h1.symm.trans h2)

/-- The carrier of a piece is the carrier of any visit of any of its labels. -/
theorem cvt165s_pieceOwner_eq_owner (hS : S ∈ Ind hP) (H : Piece hP S) {x : Crossing P}
    (hx : x ∈ pieceLabels hP S H) (w : Visit P) (hw : w.1 = x) :
    pieceOwner hP hS H = geoOwner hP S (Sum.inr w) :=
  (pieceOwner_spec hP hS H x hx w hw).symm

variable {q : GeoComponent hP S} {v : Visit P} (hc : SingletonPieceOn hP S q v.1)

include hc in
/-- A piece of `insert c S` (read as a piece of `S`) is carried by `A` iff it is carried by one of the
two daughters. -/
theorem cvt165s_mem_piecesOn_pieceEmbedding_iff (hS : S ∈ Ind hP) (H' : Piece hP (insert v.1 S)) :
    cvt165s_pieceEmbedding hP hc.mem_U hc.labels H' ∈ piecesOn hP S q ↔
      H' ∈ piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr v)) ∨
        H' ∈ piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v))) := by
  have hS' := cvt165s_mem_Ind_insert hP hc hS
  obtain ⟨x₀, hx₀⟩ := pieceLabels_nonempty hP (insert v.1 S) H'
  have hx₀' : x₀ ∈ pieceLabels hP S (cvt165s_pieceEmbedding hP hc.mem_U hc.labels H') := by
    rw [cvt165s_pieceLabels_pieceEmbedding]
    exact hx₀
  obtain ⟨j, -, -⟩ := crossing_visits_exist x₀
  rw [mem_piecesOn_iff hP hS, mem_piecesOn_iff hP hS', mem_piecesOn_iff hP hS',
    cvt165s_pieceOwner_eq_owner hP hS _ hx₀' ⟨x₀, j⟩ rfl,
    cvt165s_pieceOwner_eq_owner hP hS' H' hx₀ ⟨x₀, j⟩ rfl]
  exact cvt165s_owner_iff hP hc hS _

include hc in
/-- **The pieces carried by `A` are the piece `{c}` and the pieces carried by the two daughters.** -/
theorem cvt165s_piecesOn_eq (hS : S ∈ Ind hP) :
    piecesOn hP S q =
      insert (pieceOf hP S v.1 hc.mem_U)
        ((piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr v)) ∪
          piecesOn hP (insert v.1 S) (geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)))).map
            (cvt165s_pieceEmbedding hP hc.mem_U hc.labels)) := by
  ext H
  rw [Finset.mem_insert, Finset.mem_map]
  by_cases h : pieceLabels hP S H = {v.1}
  · have hH : H = pieceOf hP S v.1 hc.mem_U :=
      (cvt165s_pieceLabels_eq_singleton_iff hP hc.mem_U hc.labels H).mp h
    subst hH
    exact ⟨fun _ => Or.inl rfl, fun _ => hc.owner⟩
  · obtain ⟨H', hH'⟩ := (cvt165s_mem_range_pieceEmbedding_iff hP hc.mem_U hc.labels H).mpr h
    subst hH'
    rw [cvt165s_mem_piecesOn_pieceEmbedding_iff hP hc hS H', ← Finset.mem_union]
    constructor
    · intro hT
      exact Or.inr ⟨H', hT, rfl⟩
    · rintro (h1 | ⟨H'', hH'', hE⟩)
      · exact absurd ((cvt165s_pieceLabels_eq_singleton_iff hP hc.mem_U hc.labels _).mpr h1) h
      · rw [(cvt165s_pieceEmbedding hP hc.mem_U hc.labels).injective hE] at hH''
        exact hH''

end Cvt165sProducts

section Cvt165sHomfly

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hD : Diagrammatic P)

/-- **`P_H` is a function of the labels of `H`** (lem:pieceintrinsic through
`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`): two pieces, of `S` and of `S'`, with the same
labels have the same polynomial. -/
theorem cvt165s_pieceHomfly_eq_of_labels {S S' : Finset (Crossing P)} (hS : S ∈ Ind hD.crossingGeometry)
    (hS' : S' ∈ Ind hD.crossingGeometry) (H : Piece hD.crossingGeometry S) (H' : Piece hD.crossingGeometry S')
    (h : pieceLabels hD.crossingGeometry S H = pieceLabels hD.crossingGeometry S' H') :
    pieceHomfly hn hD hS H = pieceHomfly hn hD hS' H' := by
  have hcr : geoCarrierCrossings hD.crossingGeometry (S ∪ pieceSupport hD hS H) (pieceCarrier hD hS H) =
      geoCarrierCrossings hD.crossingGeometry (S' ∪ pieceSupport hD hS' H') (pieceCarrier hD hS' H') := by
    rw [pieceCarrier_geoCarrierCrossings, pieceCarrier_geoCarrierCrossings]
    exact h
  unfold pieceHomfly pieceDiagram
  exact homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic hD)
    (pieceSupport_geoIndependent hD hS H) (pieceSupport_geoIndependent hD hS' H') _ _ hcr

/-- **`P_{{c}} = 1`** (lc:single-crossing): the piece diagram of a singleton piece is a one-circle
diagram with exactly one crossing. -/
theorem cvt165s_pieceHomfly_singleton {S : Finset (Crossing P)} (hS : S ∈ Ind hD.crossingGeometry)
    {c : Crossing P} (hcU : c ∈ U hD.crossingGeometry S)
    (hlab : pieceLabels hD.crossingGeometry S (pieceOf hD.crossingGeometry S c hcU) = {c}) :
    pieceHomfly hn hD hS (pieceOf hD.crossingGeometry S c hcU) = 1 := by
  unfold pieceHomfly
  rw [← P_eq_homfly]
  have hcc : c ∈ pieceLabels hD.crossingGeometry S (pieceOf hD.crossingGeometry S c hcU) := by
    rw [hlab]
    exact Finset.mem_singleton_self c
  let e := pieceShadowCrossingEquiv hn hD hS (pieceOf hD.crossingGeometry S c hcU)
  refine single_crossing.one_crossing _ (e.symm ⟨c, hcc⟩) (pieceDiagram_componentCount hn hD hS _) ?_
  have hmem : ∀ z : Crossing P,
      z ∈ pieceLabels hD.crossingGeometry S (pieceOf hD.crossingGeometry S c hcU) → z = c := by
    intro z hz
    rw [hlab] at hz
    exact Finset.mem_singleton.mp hz
  intro y
  apply e.injective
  apply Subtype.ext
  rw [Equiv.apply_symm_apply]
  exact hmem _ (e y).2

end Cvt165sHomfly

section Cvt165sSplitAlgebra

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : Generic P) {S : Finset (Crossing P)}
  (hS : S ∈ Ind hG.crossingGeometry) {q : GeoComponent hG.crossingGeometry S} {v : Visit P}
  (hc : SingletonPieceOn hG.crossingGeometry S q v.1)

include hc in
/-- **(c) `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}`**: the pieces are literally the same objects and `P_{{c}} = 1`. -/
theorem cvt165s_groupedPoly_split :
    groupedPoly hn hG hS q =
      groupedPoly hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)) *
        groupedPoly hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  have hone : pieceHomfly hn (hG.diagrammatic hn) hS (pieceOf hG.crossingGeometry S v.1 hc.mem_U) = 1 :=
    cvt165s_pieceHomfly_singleton hn (hG.diagrammatic hn) hS hc.mem_U hc.labels
  unfold groupedPoly
  rw [cvt165s_piecesOn_eq hG.crossingGeometry hc hS,
    Finset.prod_insert (cvt165s_pieceOf_notMem_map hG.crossingGeometry hc.mem_U hc.labels _),
    Finset.prod_map, hone, one_mul,
    Finset.prod_union (cvt165s_piecesOn_disjoint hG.crossingGeometry hS'
      (cvt165s_daughters_ne hG.crossingGeometry hc hS))]
  congr 1 <;>
    exact Finset.prod_congr rfl fun H' _ =>
      cvt165s_pieceHomfly_eq_of_labels hn (hG.diagrammatic hn) hS hS' _ H'
        (cvt165s_pieceLabels_pieceEmbedding hG.crossingGeometry hc.mem_U hc.labels H')

include hS hc in
/-- **(c) `w_{S,A} = w_{S',Λ₁} + w_{S',Λ₂} + 1`**: the same pieces, and `w({c}) = 1`. -/
theorem cvt165s_groupedWrithe_split :
    groupedWrithe hG q =
      groupedWrithe hG (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)) +
        groupedWrithe hG (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))) + 1 := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  unfold groupedWrithe
  rw [cvt165s_piecesOn_eq hG.crossingGeometry hc hS,
    Finset.sum_insert (cvt165s_pieceOf_notMem_map hG.crossingGeometry hc.mem_U hc.labels _),
    Finset.sum_map, cvt165s_pieceWrithe_singleton hG.crossingGeometry hc.mem_U hc.labels,
    Finset.sum_union (cvt165s_piecesOn_disjoint hG.crossingGeometry hS'
      (cvt165s_daughters_ne hG.crossingGeometry hc hS))]
  simp only [cvt165s_pieceWrithe_pieceEmbedding hG.crossingGeometry hc.mem_U hc.labels]
  ring

end Cvt165sSplitAlgebra

/-! (d)–(e) Rotation additivity and the sign patterns: the real principal turn and the turn sign of a corner
are functions of its corner MARK and of the support only. -/

section Cvt165sRot

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- The real principal turn of a corner mark: the principal angle from the original incoming direction to
the original outgoing direction (lem:carriers (ii)). -/
noncomputable def cvt165s_markPrincipalTurn (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1)

/-- The turn sign of a corner mark. -/
noncomputable def cvt165s_markTurn (S : Finset (Crossing P)) (m : Mark P) : SignType :=
  SignType.sign (det (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1))

/-- The principal turn of the corner polygon at its `k`-th corner is the mark principal turn of that corner
(both corner edges are positive multiples of the original directions). -/
theorem cvt165s_principalTurn_eq_mark (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    principalTurn (geoCornerPolygon hP S q) k = cvt165s_markPrincipalTurn hP S (geoCornerMark hP S q k) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred_smul hn hP hS q k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  unfold principalTurn cvt165s_markPrincipalTurn
  rw [he₁, he₂, principalAngle_smul hc₁ hc₂]

theorem cvt165s_turn_eq_mark (hn : 3 ≤ n) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = cvt165s_markTurn hP S (geoCornerMark hP S q k) :=
  geoCornerPolygon_turn_eq_sign_of_independent hn hP hS q k

/-- The corner marks of the carrier `q` at `S` as a finset: the true corners of `S` owned by `q`. -/
noncomputable def cvt165s_cornerSet (S : Finset (Crossing P)) (q : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => geoOwner hP S m = q ∧ IsTrueCorner S m

theorem cvt165s_mem_cornerSet (S : Finset (Crossing P)) (q : GeoComponent hP S) (m : Mark P) :
    m ∈ cvt165s_cornerSet hP S q ↔ geoOwner hP S m = q ∧ IsTrueCorner S m := by
  simp only [cvt165s_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `geoCornerMark` enumerates the corner set exactly once. -/
theorem cvt165s_image_cornerMark (S : Finset (Crossing P)) (q : GeoComponent hP S) :
    Finset.univ.image (geoCornerMark hP S q) = cvt165s_cornerSet hP S q := by
  ext m
  rw [Finset.mem_image, cvt165s_mem_cornerSet]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact geoCornerMark_mem hP S q k
  · rintro ⟨h1, h2⟩
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q m h1 h2
    exact ⟨k, Finset.mem_univ _, hk⟩

/-- A sum over the corners of `q` is a sum over its corner-mark finset. -/
theorem cvt165s_sum_corners (S : Finset (Crossing P)) (q : GeoComponent hP S) (f : Mark P → ℝ) :
    ∑ k, f (geoCornerMark hP S q k) = ∑ m ∈ cvt165s_cornerSet hP S q, f m := by
  rw [← cvt165s_image_cornerMark, Finset.sum_image]
  intro i _ j _ hij
  exact geoCornerMark_injective hP S q hij

/-- **Inherited corners keep their principal turn** under `S → insert c S`: the incoming edge is
support-free and the outgoing slot of a true corner of `S` is unchanged. -/
theorem cvt165s_markPrincipalTurn_insert (S : Finset (Crossing P)) (c : Crossing P) (m : Mark P)
    (hm : IsTrueCorner S m) :
    cvt165s_markPrincipalTurn hP (insert c S) m = cvt165s_markPrincipalTurn hP S m := by
  unfold cvt165s_markPrincipalTurn
  cases m with
  | inl i => rw [geoOutSlot_vertex, geoOutSlot_vertex]
  | inr w =>
    have hw : w.1 ∈ S := hm
    rw [geoOutSlot_selected hP S w hw, geoOutSlot_selected hP (insert c S) w (Finset.mem_insert_of_mem hw)]

/-- The same for the turn sign. -/
theorem cvt165s_markTurn_insert (S : Finset (Crossing P)) (c : Crossing P) (m : Mark P)
    (hm : IsTrueCorner S m) :
    cvt165s_markTurn hP (insert c S) m = cvt165s_markTurn hP S m := by
  unfold cvt165s_markTurn
  cases m with
  | inl i => rw [geoOutSlot_vertex, geoOutSlot_vertex]
  | inr w =>
    have hw : w.1 ∈ S := hm
    rw [geoOutSlot_selected hP S w hw, geoOutSlot_selected hP (insert c S) w (Finset.mem_insert_of_mem hw)]

/-- **The two smoothing corners of a selected crossing cancel** in the real turn ledger: their principal
angles are `∠(d_i, d_j)` and `∠(d_j, d_i)` on a transverse pair (G5). -/
theorem cvt165s_new_turns_cancel (hn : 3 ≤ n) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    cvt165s_markPrincipalTurn hP S (Sum.inr v) + cvt165s_markPrincipalTurn hP S (Sum.inr (visitTwin v)) = 0 := by
  have hdet := geo_visit_corner_det_ne_zero hn hP S v hv
  have hv' : (visitTwin v).1 ∈ S := by
    rw [visitTwin_crossing]
    exact hv
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv] at hdet
  unfold cvt165s_markPrincipalTurn
  rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hv, geoInEdge_visit hn hP (visitTwin v),
    geoOutSlot_selected hP S (visitTwin v) hv', visitTwin_involutive,
    principalAngle_swap (regularPair_of_det_ne_zero hdet)]
  ring

/-- The turn sign at a selected visit is nonzero (transversality). -/
theorem cvt165s_markTurn_visit_ne_zero (hn : 3 ≤ n) (S : Finset (Crossing P)) (v : Visit P) (hv : v.1 ∈ S) :
    cvt165s_markTurn hP S (Sum.inr v) ≠ 0 :=
  sign_ne_zero.mpr (geo_visit_corner_det_ne_zero hn hP S v hv)

/-- The true corners of `insert c S` are those of `S` and the two visits of `c`. -/
theorem cvt165s_isTrueCorner_insert (S : Finset (Crossing P)) (c : Crossing P) (v₀ : Visit P)
    (hv₀ : v₀.1 = c) (m : Mark P) :
    IsTrueCorner (insert c S) m ↔ IsTrueCorner S m ∨ m = Sum.inr v₀ ∨ m = Sum.inr (visitTwin v₀) := by
  cases m with
  | inl i => exact ⟨fun _ => Or.inl trivial, fun _ => trivial⟩
  | inr w =>
    rw [isTrueCorner_visit, isTrueCorner_visit, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · right
        rcases visit_eq_or_twin v₀ w (h.trans hv₀.symm) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr h
      · left
        rw [Sum.inr.inj h]
        exact hv₀
      · left
        rw [Sum.inr.inj h, visitTwin_crossing]
        exact hv₀

theorem cvt165s_cornerSet_disjoint (S : Finset (Crossing P)) {q r : GeoComponent hP S} (hqr : q ≠ r) :
    Disjoint (cvt165s_cornerSet hP S q) (cvt165s_cornerSet hP S r) := by
  rw [Finset.disjoint_left]
  intro m hq hr
  rw [cvt165s_mem_cornerSet] at hq hr
  exact hqr (hq.1.symm.trans hr.1)

/-- **The corner ledger of the split**: the corner marks of the two daughters at `insert c S` are the corner
marks of `A` at `S` together with the two visits of `c`. -/
theorem cvt165s_cornerSet_union (S : Finset (Crossing P)) (q : GeoComponent hP S) (v₀ : Visit P)
    (hown0 : ∀ w : Visit P, w.1 = v₀.1 → geoOwner hP S (Sum.inr w) = q)
    (q₁ q₂ : GeoComponent hP (insert v₀.1 S))
    (hown : ∀ m : Mark P, geoOwner hP S m = q ↔
      geoOwner hP (insert v₀.1 S) m = q₁ ∨ geoOwner hP (insert v₀.1 S) m = q₂) :
    cvt165s_cornerSet hP (insert v₀.1 S) q₁ ∪ cvt165s_cornerSet hP (insert v₀.1 S) q₂ =
      cvt165s_cornerSet hP S q ∪ {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  ext m
  rw [Finset.mem_union, Finset.mem_union, cvt165s_mem_cornerSet, cvt165s_mem_cornerSet,
    cvt165s_mem_cornerSet, Finset.mem_insert, Finset.mem_singleton,
    cvt165s_isTrueCorner_insert S v₀.1 v₀ rfl m, ← or_and_right, ← hown m]
  have hA₀ : geoOwner hP S (Sum.inr v₀) = q := hown0 v₀ rfl
  have hA₁ : geoOwner hP S (Sum.inr (visitTwin v₀)) = q := hown0 (visitTwin v₀) (visitTwin_crossing v₀)
  constructor
  · rintro ⟨hm, hT | hm₀ | hm₁⟩
    · exact Or.inl ⟨hm, hT⟩
    · exact Or.inr (Or.inl hm₀)
    · exact Or.inr (Or.inr hm₁)
  · rintro (⟨hm, hT⟩ | rfl | rfl)
    · exact ⟨hm, Or.inl hT⟩
    · exact ⟨hA₀, Or.inr (Or.inl rfl)⟩
    · exact ⟨hA₁, Or.inr (Or.inr rfl)⟩

/-- The two visits of the unselected `c` are not corners of `S`. -/
theorem cvt165s_cornerSet_disjoint_visits (S : Finset (Crossing P)) (q : GeoComponent hP S) (v₀ : Visit P)
    (hcS : v₀.1 ∉ S) :
    Disjoint (cvt165s_cornerSet hP S q) {Sum.inr v₀, Sum.inr (visitTwin v₀)} := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  rw [cvt165s_mem_cornerSet] at hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm'
  rcases hm' with rfl | rfl
  · exact hcS hm.2
  · exact hcS ((visitTwin_crossing v₀) ▸ hm.2)

end Cvt165sRot



section Cvt165sDaughterPattern

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hP : CrossingGeometry P) (hn : 3 ≤ n)
  {S : Finset (Crossing P)} (hS : S ∈ Ind hP) {q : GeoComponent hP S} {v : Visit P}
  (hc : SingletonPieceOn hP S q v.1)

include hn hS hc in
/-- **The signed turn pattern of a daughter.** Every corner of the daughter `Λ` other than its visit `w` of
`c` is a corner of `A` (owned by `A`, a true corner of `S`), hence turns by `τ`; the corner at `w` turns by
`markTurn (inr w) ∈ {τ, −τ}`. -/
theorem cvt165s_daughter_pattern (Λ : GeoComponent hP (insert v.1 S))
    (hΛ : Λ = geoOwner hP (insert v.1 S) (Sum.inr v) ∨ Λ = geoOwner hP (insert v.1 S) (Sum.inr (visitTwin v)))
    (w : Visit P) (hw : w.1 = v.1) (hwΛ : geoOwner hP (insert v.1 S) (Sum.inr w) = Λ)
    (τ : SignType) (hτ0 : τ ≠ 0) (hτ : ∀ k, turn (geoCornerPolygon hP S q) k = τ) :
    (∀ k, turn (geoCornerPolygon hP (insert v.1 S) Λ) k = τ) ∨
      (∃ k₀, turn (geoCornerPolygon hP (insert v.1 S) Λ) k₀ = -τ ∧
        ∀ k, k ≠ k₀ → turn (geoCornerPolygon hP (insert v.1 S) Λ) k = τ) := by
  have hind : GeoIndependent hP S := geoIndependent_of_mem_Ind hP hS
  have hind' : GeoIndependent hP (insert v.1 S) := cvt165s_geoIndependent_insert hP hc hS
  have hwS' : w.1 ∈ insert v.1 S := by
    rw [hw]
    exact Finset.mem_insert_self _ _
  have hwT : IsTrueCorner (insert v.1 S) (Sum.inr w) := hwS'
  -- every corner of `Λ` other than `inr w` is an inherited corner of `A`, of turn `τ`
  have hother : ∀ k, geoCornerMark hP (insert v.1 S) Λ k ≠ Sum.inr w →
      turn (geoCornerPolygon hP (insert v.1 S) Λ) k = τ := by
    intro k hk
    rw [cvt165s_turn_eq_mark hP hn hind' Λ k]
    obtain ⟨hmΛ, hmT'⟩ := geoCornerMark_mem hP (insert v.1 S) Λ k
    have hmA : geoOwner hP S (geoCornerMark hP (insert v.1 S) Λ k) = q := by
      apply cvt165s_owner_of_insert hP hc
      rcases hΛ with hΛ | hΛ
      · exact Or.inl (hmΛ.trans hΛ)
      · exact Or.inr (hmΛ.trans hΛ)
    rcases (cvt165s_isTrueCorner_insert S v.1 w hw _).mp hmT' with hT | hmw | hmw
    · obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hP S q _ hmA hT
      rw [cvt165s_markTurn_insert hP S v.1 _ hT, ← hk', ← cvt165s_turn_eq_mark hP hn hind q k']
      exact hτ k'
    · exact absurd hmw hk
    · exfalso
      apply geo_selected_visits_separated hP hind' w hwS'
      rw [hwΛ, ← hmw]
      exact hmΛ.symm
  -- the corner at `w`
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hP (insert v.1 S) Λ (Sum.inr w) hwΛ hwT
  have hk₀turn : turn (geoCornerPolygon hP (insert v.1 S) Λ) k₀ =
      cvt165s_markTurn hP (insert v.1 S) (Sum.inr w) := by
    rw [cvt165s_turn_eq_mark hP hn hind' Λ k₀, hk₀]
  have hw0 : cvt165s_markTurn hP (insert v.1 S) (Sum.inr w) ≠ 0 :=
    cvt165s_markTurn_visit_ne_zero hP hn (insert v.1 S) w hwS'
  rcases cvt165s_signType_eq_or_neg hw0 hτ0 with h | h
  · left
    intro k
    by_cases hk : geoCornerMark hP (insert v.1 S) Λ k = Sum.inr w
    · have hkk : k = k₀ := geoCornerMark_injective hP _ Λ (hk.trans hk₀.symm)
      rw [hkk, hk₀turn, h]
    · exact hother k hk
  · right
    refine ⟨k₀, by rw [hk₀turn, h], fun k hk => hother k fun hk' => ?_⟩
    exact hk (geoCornerMark_injective hP _ Λ (hk'.trans hk₀.symm))

end Cvt165sDaughterPattern

section Cvt165sSplitRot

variable {n : ℕ} [NeZero n] {P : LabelledTuple n} (hn : 3 ≤ n) (hG : Generic P) {S : Finset (Crossing P)}
  (hS : S ∈ Ind hG.crossingGeometry) {q : GeoComponent hG.crossingGeometry S}

/-- **`2π rot(L) = Σ` over the corner marks of `L`** of the mark principal turn. -/
theorem cvt165s_two_pi_rot (q : GeoComponent hG.crossingGeometry S) :
    2 * Real.pi * (rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) : ℝ) =
      ∑ m ∈ cvt165s_cornerSet hG.crossingGeometry S q, cvt165s_markPrincipalTurn hG.crossingGeometry S m := by
  rw [two_pi_mul_rot, ← cvt165s_sum_corners]
  exact Finset.sum_congr rfl fun k _ =>
    cvt165s_principalTurn_eq_mark hG.crossingGeometry hn (geoIndependent_of_mem_Ind _ hS) q k

variable {v : Visit P} (hc : SingletonPieceOn hG.crossingGeometry S q v.1)

include hc in
/-- **(d), real form: `rot(A) = rot(Λ₁) + rot(Λ₂)`** — every inherited corner keeps its principal turn and
the two new smoothing corners cancel. -/
theorem cvt165s_rot_add :
    (rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) : ℝ) =
      rot (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)))
          (carrierPolygon_cvRegular hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS) _) +
        rot (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))))
          (carrierPolygon_cvRegular hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS) _) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  have hvne : (Sum.inr v : Mark P) ≠ Sum.inr (visitTwin v) := by
    intro h
    exact visitTwin_ne v (Sum.inr.inj h).symm
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2π
  rw [mul_add, cvt165s_two_pi_rot hn hG hS q, cvt165s_two_pi_rot hn hG hS', cvt165s_two_pi_rot hn hG hS',
    ← Finset.sum_union (cvt165s_cornerSet_disjoint _ _ (cvt165s_daughters_ne _ hc hS)),
    cvt165s_cornerSet_union _ S q v (fun w hw => cvt165s_owner_visit _ hc w hw) _ _
      (cvt165s_owner_iff _ hc hS),
    Finset.sum_union (cvt165s_cornerSet_disjoint_visits _ S q v (cvt165s_notMem _ hc)),
    Finset.sum_pair hvne, cvt165s_new_turns_cancel _ hn (insert v.1 S) v (Finset.mem_insert_self _ _),
    add_zero]
  exact Finset.sum_congr rfl fun m hm =>
    (cvt165s_markPrincipalTurn_insert _ S v.1 m ((cvt165s_mem_cornerSet _ S q m).mp hm).2).symm

include hn hS hc in
/-- The daughter patterns, at the two daughters. -/
theorem cvt165s_daughter_patterns (hq : CarrierUniform hG.crossingGeometry S q) :
    ∃ τ : SignType, τ ≠ 0 ∧
      (∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = τ) ∧
      ((∀ k, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) k = τ) ∨
        (∃ k₀, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) k₀ = -τ ∧
          ∀ k, k ≠ k₀ → turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) k = τ)) ∧
      ((∀ k, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) k = τ) ∨
        (∃ k₀, turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) k₀ = -τ ∧
          ∀ k, k ≠ k₀ → turn (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
            (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) k = τ)) := by
  obtain ⟨τ, hτ0, hτ⟩ := hq
  exact ⟨τ, hτ0, hτ,
    cvt165s_daughter_pattern hG.crossingGeometry hn hS hc _ (Or.inl rfl) v rfl rfl τ hτ0 hτ,
    cvt165s_daughter_pattern hG.crossingGeometry hn hS hc _ (Or.inr rfl) (visitTwin v) (visitTwin_crossing v)
      rfl τ hτ0 hτ⟩

include hc in
/-- **(d) `R(A) = R(Λ₁) + R(Λ₂)`**: the real rotations add and all three lie on the ray of `A`'s sign
(lem:uniformrot), so the absolute values add. -/
theorem cvt165s_carrierR_split (hq : CarrierUniform hG.crossingGeometry S q) :
    (carrierR hn hG hS q : ℤ) =
      carrierR hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v)) +
        carrierR hn hG (cvt165s_mem_Ind_insert hG.crossingGeometry hc hS)
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v))) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  obtain ⟨τ, hτ0, -, hp₁, hp₂⟩ := cvt165s_daughter_patterns hn hG hS hc hq
  have hsum := cvt165s_rot_add hn hG hS hc
  have hsumZ : rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) =
      rot _ (carrierPolygon_cvRegular hn hG hS' (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) +
        rot _ (carrierPolygon_cvRegular hn hG hS'
          (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) := by
    exact_mod_cast hsum
  have hr₁ := cvt165s_rot_ray _ (carrierPolygon_cvRegular hn hG hS' _) τ hp₁
  have hr₂ := cvt165s_rot_ray _ (carrierPolygon_cvRegular hn hG hS' _) τ hp₂
  rw [carrierR_cast, carrierR_cast, carrierR_cast, hsumZ]
  rcases SignType.trichotomy τ with rfl | rfl | rfl
  · exact (cvt165s_abs_add_of_ray _ _).1 (hr₁.2 rfl) (hr₂.2 rfl)
  · exact absurd rfl hτ0
  · exact (cvt165s_abs_add_of_ray _ _).2 (hr₁.1 rfl) (hr₂.1 rfl)

include hn hS hc in
/-- **(e)** Both daughters are uniform or one-dissent after reversal. -/
theorem cvt165s_daughters_alt (hq : CarrierUniform hG.crossingGeometry S q) :
    UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
        (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr v))) ∧
      UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry (insert v.1 S)
        (geoOwner hG.crossingGeometry (insert v.1 S) (Sum.inr (visitTwin v)))) := by
  have hS' := cvt165s_mem_Ind_insert hG.crossingGeometry hc hS
  obtain ⟨τ, hτ0, -, hp₁, hp₂⟩ := cvt165s_daughter_patterns hn hG hS hc hq
  exact ⟨cvt165s_uniformOrOneDissent_of_pattern _ (carrierPolygon_cvRegular hn hG hS' _) τ hτ0 hp₁,
    cvt165s_uniformOrOneDissent_of_pattern _ (carrierPolygon_cvRegular hn hG hS' _) τ hτ0 hp₂⟩

end Cvt165sSplitRot

end Cvt165s


/-- LEAF (unit U-SPLIT, ~1.5-2.5k lines): the split interface on the geo layer. -/
theorem cvt_singleton_split : SingletonSplitData := by
  intro n _ hn P hG S hS q hq c hc
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  have hc' : SingletonPieceOn hG.crossingGeometry S q (⟨c, i⟩ : Visit P).1 := hc
  rw [cvt165s_insert_eq c S]
  exact ⟨cvt165s_mem_Ind_insert hG.crossingGeometry hc' hS, _, _,
    cvt165s_groupedPoly_split hn hG hS hc', cvt165s_groupedWrithe_split hG hS hc',
    cvt165s_carrierR_split hn hG hS hc' hq, (cvt165s_daughters_alt hn hG hS hc' hq).1,
    (cvt165s_daughters_alt hn hG hS hc' hq).2⟩

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
