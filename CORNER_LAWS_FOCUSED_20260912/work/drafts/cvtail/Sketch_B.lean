import RProof.X1Rows2
import RProof.GenericTransport
import Bridge.SmR
import CV.UniformRot
import CV.Curl
import CV.Rounding
import CV.GroupedKnot
import CV.ChamberInvRow
import CV.Axioms
import SM.CS5
import SM.CS3
import SM.CSilent
import SM.CChamber
import SM.ALawful
import SM.RotationReversal

/-! # CV/R tail (rows 155, 165, 174-178, 183, 184) — design sketch B (proof feasibility / assembly)

Companion of work/drafts/cvtail/DESIGN_B.md.  Check: `cd work/lean && lake env lean ../drafts/cvtail/Sketch_B.lean`.
STATEMENTS carry no `sorry`; proof leaves are `sorry` (design, not a proof) except the parts marked
PROVED (row 155 clause (D); the row-178 assembly `RProof.cv_R_of_rows`; row 183; the row-184 assembly
`SM.corner_laws_and_soft_of`).  Nothing here is to be ported without the rows' statement reviews.
Helper prefix of this lane: `cvt_`.  Interfaces copied from sibling lanes are marked "to be unified". -/

namespace SM

open Link
open scoped ContDiff

noncomputable section
open Classical

/-! ## 0. Assumed interface — SM row 99 cf:thm-carrierfloor, clauses (R)(A)(B)(C)
(copied from work/drafts/floor/Sketch_A.lean §2-§6; TO BE UNIFIED WITH LANE FLOOR).  Row 155's clauses
(R)(A)(B)(C) are these read through the polygon bridge of CV/Rounding.lean §1 (rule F6). -/

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

def TangencyCount {C : PolyComp} {D : PolygonDiagram C} {ε : ℝ} (W : RoundingWitness C D ε)
    (u : Plane) (R : ℝ) : Prop :=
  {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}.Finite ∧
  (({t | t ∈ Set.Ico (0 : ℝ) 1 ∧ W.T t = u}.ncard : ℝ) = R) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) 1, W.T t = u →
    ∃ j, j < C.k ∧ t ∈ Set.Ioo (W.a j) (W.b j) ∧ 0 < deriv (W.θ j) t

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

structure CarrierFloorCData : Prop where
  floor : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (P X) : ℝ)
  floor_zZero : ∀ (C : PolyComp) (X : Diagram), CarrierFloorCHyp C X → zZeroPart (P X) ≠ 0 →
    ((1 - X.writhe : ℤ) : ℝ) - |rotationNumber C.P| ≤ (mindegAZ (zZeroPart (P X)) : ℝ)

/-- SM row 99 bundle (proposed `SM.cf_thm_carrierfloor : CarrierFloorData`, lane floor). -/
structure CarrierFloorData : Prop where
  clauseR : CarrierFloorRData
  clauseA : CarrierFloorAData
  clauseB : CarrierFloorBData
  clauseC : CarrierFloorCData

end

end SM

namespace CV

open SM SM.Link SM.Carrier SM.GeoCarrier

noncomputable section
open Classical

variable {n : ℕ} [NeZero n]

/-! ## 1. Row 155 CV:thm:carrierfloor (d3_floor.tex:736-807) — the CV statement

Clauses (R)(A)(B)(C) are SM row 99's clauses read on CV's printed binders through the polygon bridge
(`polyComp`, `OverUnder.toPolygonDiagram`, `roundingRecord`, `clearance` of CV/Rounding.lean; `rot` =
CV:def:rot via `rot_eq_rotationNumber`; `P_D` = CV:def:homfly's `homfly` via `P_eq_homfly`).  Clause (D)
is on def:X1's objects (CV/X1.lean).  Readings FR-CV-1..7 in DESIGN_B.md §1. -/

/-- "either every principal turn is positive, or exactly one is negative and every other is positive"
(CV:def:regular's `principalTurn`; equal to SM's by `principalTurn_eq_sm`). -/
def AllPosOrOneNegCV {c : ℕ} (L : LabelledTuple c) : Prop :=
  (∀ i, 0 < principalTurn L i) ∨
  (∃ i, principalTurn L i < 0 ∧ ∀ j, j ≠ i → 0 < principalTurn L j)

/-- "after reversing the orientation if necessary, either …" (reversal negates every principal turn,
`principalTurn_reversal`). -/
def UniformOrOneDissentCV {c : ℕ} (L : LabelledTuple c) : Prop :=
  AllPosOrOneNegCV L ∨ AllPosOrOneNegCV (reversal L)

/-- Clause (R) in CV's letters: the polygon `rot` is CV:def:rot's `rot` (`rot_reversal`), the curve `rot`
is `rotCurve` (= `ClosedC1Curve.rot`, F6); the polynomial is `homfly` (CV:def:homfly). -/
structure CarrierFloorRDataCV : Prop where
  P_reverse : ∀ X : Diagram, X.componentCount = 1 → homfly X.reverse = homfly X
  knot_reverse : ∀ X X' : Diagram, X.componentCount = 1 → LinkEquiv X X' → homfly X'.reverse = homfly X
  sign_reverse : ∀ (X : Diagram) (x : X.Γ.reverseShadow.Crossing),
    X.reverse.sign x = X.sign (X.Γ.reverseCrossingEquiv x)
  writhe_reverse : ∀ X : Diagram, X.reverse.writhe = X.writhe
  rot_reverse_polygon : ∀ {c : ℕ} [NeZero c] (L : LabelledTuple c) (hL : Regular L),
    rot (reversal L) (regular_reversal' hL) = -rot L hL
  rot_reverse_curve : ∀ γ : ClosedC1Curve, rotCurve γ.reverse = -rotCurve γ

/-- The record `Round(L, D, ε)` on CV's binders is `roundingRecord` (CV/Rounding.lean §2). -/
abbrev Rnd {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) :
    RoundingWitness (polyComp L hreg) (D.toPolygonDiagram hL) ε :=
  roundingRecord hL hreg hturn D hε hε₀

/-- Clause (A) on CV's binders ("Let L and D satisfy the hypotheses of Lemma lem:rounding"): SM's fields
at `C := polyComp L hreg`, `D := D.toPolygonDiagram hL`, `Round := roundingRecord`. -/
structure CarrierFloorADataCV : Prop where
  one_record : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    Rnd hL hreg hturn D hε hε₀ =
      SM.Round (polyComp L hreg) (D.toPolygonDiagram hL) ε (roundingAdmissible hL hreg hturn D hε hε₀)
  one_curve : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    (Rnd hL hreg hturn D hε hε₀).Lε = CornerRounding.roundedLoop (roundingAdmissible hL hreg hturn D hε hε₀)
  one_diagram : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    Nonempty (Carried (Rnd hL hreg hturn D hε hε₀).Lε (D.toPolygonDiagram hL).toDiagram) ∧
    (Rnd hL hreg hturn D hε hε₀).carried.smoothWrithe = (D.toPolygonDiagram hL).toDiagram.writhe
  junction_determined : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) (j : ℕ), j < n → ∀ s ∈ Set.Icc (0 : ℝ) 1,
    (Rnd hL hreg hturn D hε hε₀).Lε.γ ((Rnd hL hreg hturn D hε hε₀).a j +
        s * ((Rnd hL hreg hturn D hε hε₀).b j - (Rnd hL hreg hturn D hε hε₀).a j)) =
      SM.junctionTemplate (L j) (CornerRounding.uDir (polyComp L hreg) j)
        (CornerRounding.vDir (polyComp L hreg) j) ε s
  length_determined : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg) (j : ℕ), j < n →
    (Rnd hL hreg hturn D hε hε₀).speed * ((Rnd hL hreg hturn D hε hε₀).b j - (Rnd hL hreg hturn D hε hε₀).a j) =
        CornerRounding.juncLen ε (principalTurn L j) ∧
    (Rnd hL hreg hturn D hε hε₀).Lε.γ ((Rnd hL hreg hturn D hε hε₀).b j) =
      L j + ε • CornerRounding.vDir (polyComp L hreg) j
  rest_is_L : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) (ε : ℝ)
    (hε : 0 < ε) (hε₀ : ε < clearance L hreg),
    (∀ p : Plane, p ∉ (⋃ i, cornerDisc (polyComp L hreg) ε i) →
      (p ∈ Set.range (Rnd hL hreg hturn D hε hε₀).Lε.γ ↔ p ∈ ⋃ i : ZMod n, edgeSegment L i)) ∧
    ∀ j < n, ∀ t ∈ Set.Icc ((Rnd hL hreg hturn D hε hε₀).b j) ((Rnd hL hreg hturn D hε hε₀).a (j + 1)),
      (Rnd hL hreg hturn D hε hε₀).Lε.γ t = (Rnd hL hreg hturn D hε hε₀).Lε.γ ((Rnd hL hreg hturn D hε hε₀).b j) +
        ((Rnd hL hreg hturn D hε hε₀).speed * (t - (Rnd hL hreg hturn D hε hε₀).b j)) • normalize (edge L j)

/-- Clause (B)'s claim on CV's binders, `R = |rot(L)|` = `rotAbs L hreg` (CV:def:rot), `ε₁ ≤ ε₀(L)`
(`clearance L hreg`), the record `Rnd` at every `ε ∈ (0, ε₁)`. -/
def BClaimCV {L : LabelledTuple n} (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)) : Prop :=
  ∃ (u : Plane) (ε₁ : ℝ) (_hu : euclideanLength u = 1) (_hpos : 0 < ε₁) (hle : ε₁ ≤ clearance L hreg),
    ∀ (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < ε₁),
      SM.TangencyCount (Rnd hL hreg hturn D hε (hε₁.trans_le hle)) u (rotAbs L hreg) ∧
      SM.TangencyCount (Rnd hL hreg hturn D hε (hε₁.trans_le hle)) (-u) (rotAbs L hreg)

/-- Clause (B) ("Let L be a diagrammatic closed polygon whose principal turns all exist and are nonzero,
carrying a diagram D"): the normalised branch on CV's binders; the reversal branch on SM's objects through
the bridge (FR-CV-B2: `OverUnder.reverse` is not in the library; to be unified with lane floor's
`CarrierFloorBData`). -/
structure CarrierFloorBDataCV : Prop where
  tangencies : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hL : Diagrammatic L) (hreg : Regular L)
    (hturn : ∀ i, principalTurn L i ≠ 0) (D : OverUnder (polyComp L hreg)),
    UniformOrOneDissentCV L →
    (AllPosOrOneNegCV L ∧ BClaimCV hL hreg hturn D) ∨
    (AllPosOrOneNegCV (reversal L) ∧
      SM.BClaim (polyComp L hreg).reverse (D.toPolygonDiagram hL).reverse)

/-- Clause (C) on CV's binders: the polygon `L` is CV's labelled tuple (`polyComp L hreg`), `R = rotAbs L
hreg`, `P_D = homfly X`; the hypothesis list is SM's `CarrierFloorCHyp` at `polyComp L hreg`. -/
structure CarrierFloorCDataCV : Prop where
  floor : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) (X : Diagram),
    SM.CarrierFloorCHyp (polyComp L hreg) X →
    (1 - X.writhe : ℤ) - (rotAbs L hreg : ℤ) ≤ mindegAZ (homfly X)
  floor_zZero : ∀ {n : ℕ} [NeZero n] (L : LabelledTuple n) (hreg : Regular L) (X : Diagram),
    SM.CarrierFloorCHyp (polyComp L hreg) X → SM.zZeroPart (homfly X) ≠ 0 →
    (1 - X.writhe : ℤ) - (rotAbs L hreg : ℤ) ≤ mindegAZ (SM.zZeroPart (homfly X))

/-- Clause (D) (d3:794-806): "Let P be generic, S ∈ Ind(G_P), L a carrier of S carrying no residual piece
(P_{S,L} = 1, w_{S,L} = 0 by def:X1's empty conventions), all principal turns nonzero and, after reversing
if necessary, uniform or one-dissent.  Then R(L) ≥ 1 and min deg_a P_{S,L} = 0 ≥ 1 − w_{S,L} − R(L)." -/
structure CarrierFloorDData : Prop where
  clauseD : ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    piecesOn hG.crossingGeometry S q = ∅ →
    (∀ j, principalTurn (geoCornerPolygon hG.crossingGeometry S q) j ≠ 0) →
    UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q) →
    1 ≤ carrierR hn hG hS q ∧ mindegAZ (groupedPoly hn hG hS q) = 0 ∧ slot hn hG hS q ≤ 0

/-- **Row 155, CV:thm:carrierfloor** (proposed name `CV.carrierfloor : CarrierFloorDataCV`). -/
structure CarrierFloorDataCV : Prop where
  clauseR : CarrierFloorRDataCV
  clauseA : CarrierFloorADataCV
  clauseB : CarrierFloorBDataCV
  clauseC : CarrierFloorCDataCV
  clauseD : CarrierFloorDData

/-! ### 1.1 Clause (D) — PROVED NOW (CV:lem:uniformrot + def:X1's empty conventions) -/

/-- `|rot L| ≥ 1` under the four-way alternative (the printed "in the uniform case … uniformrot (i); in the
one-dissent case … uniformrot (ii)", after reversal `rot_reversal`). -/
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

/-- Clause (D). -/
theorem carrierfloor_D : CarrierFloorDData where
  clauseD := by
    intro n _ hn P hG S hS q hempty _ halt
    have hR := cvt_one_le_rotAbs_of_alt _ (carrierPolygon_cvRegular hn hG hS q) halt
    refine ⟨hR, ?_, ?_⟩
    · rw [groupedPoly_of_piecesOn_eq_empty hn hG hS q hempty]; exact cvt_mindegAZ_one
    · unfold slot
      rw [groupedWrithe_of_piecesOn_eq_empty hG q hempty]
      have : (1 : ℤ) ≤ (carrierR hn hG hS q : ℤ) := by exact_mod_cast hR
      omega

/-! ### 1.2 Clauses (R)(A)(B)(C) from SM row 99 through the bridge (leaves; DESIGN_B.md §2.1) -/

theorem cvt_R_of_sm (h : SM.CarrierFloorRData) : CarrierFloorRDataCV where
  P_reverse := fun X hc => by rw [← P_eq_homfly, ← P_eq_homfly]; exact h.P_reverse X hc
  knot_reverse := fun X X' hc he => by rw [← P_eq_homfly, ← P_eq_homfly]; exact h.knot_reverse X X' hc he
  sign_reverse := h.sign_reverse
  writhe_reverse := h.writhe_reverse
  rot_reverse_polygon := fun L hL => rot_reversal hL _
  rot_reverse_curve := fun γ => h.rot_reverse_curve γ

theorem cvt_A_of_sm (h : SM.CarrierFloorAData) : CarrierFloorADataCV := by
  sorry -- each field is SM's at `polyComp L hreg`, `D.toPolygonDiagram hL` (`roundingRecord_eq` is `rfl`)

theorem cvt_B_of_sm (h : SM.CarrierFloorBData) : CarrierFloorBDataCV := by
  sorry -- `polyComp_P`, `rot_eq_rotationNumber`, `rotAbs_cast_real`; `UniformOrOneDissentCV L ↔ SM.UniformOrOneDissent (polyComp L hreg)` by `principalTurn_eq_sm`

theorem cvt_C_of_sm (h : SM.CarrierFloorCData) : CarrierFloorCDataCV := by
  sorry -- instantiate at `polyComp L hreg`; `P_eq_homfly`; `rot_eq_rotationNumber`, `rotAbs_cast_real`; cast to ℤ

/-- Row 155 from SM row 99 (the polygon bridge) and clause (D). -/
theorem carrierfloor_of_sm (h : SM.CarrierFloorData) : CarrierFloorDataCV where
  clauseR := cvt_R_of_sm h.clauseR
  clauseA := cvt_A_of_sm h.clauseA
  clauseB := cvt_B_of_sm h.clauseB
  clauseC := cvt_C_of_sm h.clauseC
  clauseD := carrierfloor_D

/-! ### 1.3 The consumer corollary of (C)+(D): the carrier floor in def:X1's symbols.
Rows 165, 174, 176, 177 consume ONLY this (DESIGN_B.md §2.2): "no exponent below the slot occurs in
`f_L = [z⁰] P_{S,L}`", for every carrier `L` of a `CV.Generic` polygon that is uniform or one-dissent. -/

/-- The carrier floor in def:X1's symbols (library theorem; not a row). -/
def CarrierSlotFloor : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    UniformOrOneDissentCV (geoCornerPolygon hG.crossingGeometry S q) →
    ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q ≤ d

/-- Route: piece-free carrier — clause (D) (`groupedPoly = 1`, so `d = 0 ≥ slot`); carrier with pieces —
cor:groupedknot (B) (`carrierDiagram` is a positive knot diagram on `geoCornerPolygon` with `homfly =
groupedPoly`, `writhe = groupedWrithe`, no triple points), `geoCarrierShadow` = `Shadow.single
(geoCarrierPolyComp …)` (`geoPositiveLift_Γ`), turns nonzero (`geoCornerPolygon_turn_ne_zero`),
`|turn| < π` (`principalAngle_bounds`), then clause (C)'s `floor` with `rot_eq_rotationNumber`,
`rotAbs_cast_real` and `mindegAZ_spec`. -/
theorem carrier_slot_floor_of_C (hC : SM.CarrierFloorCData) : CarrierSlotFloor := by
  sorry

/-! ## 2. Row 165 CV:singleton_D_i — thm:s7universal (D)(i) (d6_vertexedge.tex:2682-2687) -/

/-- "`{c}` a singleton residual piece of `S` carried by `A`": `c ∈ U(S)`, its piece has label set `{c}`,
and that piece is on the carrier `q` (lem:carriers (iv)). -/
structure SingletonPieceOn {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (c : Crossing P) : Prop where
  mem_U : c ∈ U hP S
  labels : pieceLabels hP S (pieceOf hP S c mem_U) = {c}
  owner : pieceOf hP S c mem_U ∈ piecesOn hP S q

/-- **Row 165 (statement).** "Let S ∈ Ind(G_P), A a uniform carrier of S, {c} a singleton residual piece
of S carried by A.  Then min deg_a f_A ≥ (1 − w_{S,A} − R(A)) + 2, so the factor Ω₁(S,A) of def:X1 is
zero."  `f_A = [z⁰] P_{S,A}` in support form (every monomial `a^d z⁰` present has `d ≥ slot + 2`;
vacuous when `f_A = 0`, FR-CV-8). -/
def SingletonDiStatement : Prop :=
  ∀ {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S),
    CarrierUniform hG.crossingGeometry S q →
    ∀ c : Crossing P, SingletonPieceOn hG.crossingGeometry S q c →
      (∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d) ∧
      Omega1 hn hG hS q = 0

/-- Interface to the corner lane (cb:singleton's splitting machinery on the shared geo layer; TO BE
UNIFIED WITH LANE CORNER): smoothing `c` splits the carrier `A` of `S` into two carriers `Λ₁, Λ₂` of
`S' = S ∪ {c}` with `P_{S,A} = P_{S',Λ₁} P_{S',Λ₂}`, `w_{S,A} = w_{S',Λ₁} + w_{S',Λ₂} + 1`,
`R(A) = R(Λ₁) + R(Λ₂)`, one loop uniform and the other one-dissent (d6:2890-2935). -/
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

/-- Knot parity of a grouped polynomial: `P_{S,L} ∈ ℤ[a^{±1}, z²]` (cor:groupedknot (B) + ax:homfly's
`knot_parity`; `InSupportM.one` when piece-free). -/
theorem cvt_groupedPoly_inSupportM (hn : 3 ≤ n) {P : LabelledTuple n} (hG : Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    InSupportM 1 (groupedPoly hn hG hS q) := by
  by_cases h : (piecesOn hG.crossingGeometry S q).Nonempty
  · rw [← ((groupedknot hn hG hS q).grouped_polynomial h).1]
    exact ax_homfly.knot_parity _ ((groupedknot hn hG hS q).knot_diagram h).1
  · rw [groupedPoly_of_piecesOn_eq_empty hn hG hS q (Finset.not_nonempty_iff_eq_empty.mp h)]
    exact InSupportM.one

/-- The `z⁰` row of a product of knot polynomials: the floors add (`zRow_zero_mul_of_inSupportM_one`). -/
theorem cvt_coeff_zero_mul_floor {f g : R} (hf : InSupportM 1 f) (hg : InSupportM 1 g) {a b : ℤ}
    (ha : ∀ d, coeffAt d 0 f ≠ 0 → a ≤ d) (hb : ∀ d, coeffAt d 0 g ≠ 0 → b ≤ d) :
    ∀ d, coeffAt d 0 (f * g) ≠ 0 → a + b ≤ d := by
  sorry

/-- **Row 165 from the split interface and the carrier floor** (the printed proof d6:2890-2947). -/
theorem singleton_D_i_of (hsplit : SingletonSplitData) (hfloor : CarrierSlotFloor) :
    SingletonDiStatement := by
  intro n _ hn P hG S hS q hq c hc
  obtain ⟨hS', q₁, q₂, hpoly, hwrithe, hrot, halt₁, halt₂⟩ := hsplit hn hG hS q hq c hc
  have hbound : ∀ d : ℤ, coeffAt d 0 (groupedPoly hn hG hS q) ≠ 0 → slot hn hG hS q + 2 ≤ d := by
    intro d hd
    rw [hpoly] at hd
    have := cvt_coeff_zero_mul_floor (cvt_groupedPoly_inSupportM hn hG hS' q₁)
      (cvt_groupedPoly_inSupportM hn hG hS' q₂) (hfloor hn hG hS' q₁ halt₁) (hfloor hn hG hS' q₂ halt₂) d hd
    unfold slot at this ⊢
    rw [hwrithe, hrot]
    linarith
  refine ⟨hbound, ?_⟩
  unfold Omega1
  by_contra h
  have := hbound _ h
  omega

end

end CV

/-! ## 3. Rows 174-178 — the R obligations (FIXED statements = the bundles of RProof/X1Rows.lean) -/

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 174, R:generic_selected** (R_GENERIC_SELECTED_COUPLE_PROOF.md).  Consumes: rows 168, 171, 172,
173's `GT_Wall` transport, CV:lem:fulltwist, CV:lem:homflyrows (ii), ax:homfly knot parity, CV:lem:turnlift
(ii), CV:lem:uniformrot, cor:groupedknot (A)(B), and `CV.CarrierSlotFloor` (the (C)+(D) corollary); plus
an RII deletion of the switched pair (G10). -/
theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ := by
  sorry

/-- The owner of a piece (lem:carriers (iv): every residual piece is carried by exactly one carrier). -/
theorem cvt_exists_owner {P : LabelledTuple n} (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (H : CV.Piece hP S) : ∃ q : GeoComponent hP S, H ∈ CV.piecesOn hP S q := by
  sorry

/-- **Row 175 from row 165** (R_EXTREME_PAIR_ZERO_PROOF.md, paragraphs 4-5): `Q ∪ J ∈ Ind` (PRE), `{z}` a
singleton piece (`PRE_175_third_singleton_piece` from `parity`), `wind = 0` or every carrier uniform
(`weight_ne_zero_iff`), and CV:singleton_D_i on the owner of `{z}` kills the product. -/
theorem extreme_pair_zero_of_singleton (h165 : CV.SingletonDiStatement) (hn : 3 ≤ n) (E : CV.Event n)
    (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ := by
  obtain ⟨δ, hδ, hδr, hPar⟩ := parity E e f g h3 h4e h4f h4g hE
  refine ⟨δ, hδ, hδr, ?_⟩
  refine ⟨PRE_175_pair_absent_on_complete E e f g δ, PRE_175_pair_present_on_empty E e f g δ,
    PRE_175_third_singleton_piece hPar, ?_⟩
  intro t ht hef heg hfg hL Q hQ hfull J hJT hJ2
  have hind := PRE_175_pair_present_on_empty E e f g δ t ht hef heg hfg hL Q hQ hfull J hJT hJ2
  rw [rowTerm_of_mem_Ind hn _ hind]
  by_cases hw : CV.wind (geomAt E t ht.1) (Q ∪ J) = 0
  · rw [hw, zero_mul]
  · -- the third crossing `z` and its singleton piece; its owner `q` is uniform since `wind ≠ 0`
    sorry

/-- **Row 175, R:extreme_pair_zero** (fixed statement). -/
theorem extreme_pair_zero (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ := by
  sorry -- `extreme_pair_zero_of_singleton CV.singleton_D_i hn E e f g h3 h4e h4f h4g hE` once row 165 lands

/-- **Row 176, R:extreme_transport** (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md).  Consumes: rows 168, 171,
173's `GT_Wall`/`GT_Relabel`, CV:selector_A, CV:lem:fulltwist, CV:lem:homflyrows (ii), knot parity,
turnlift (ii), uniformrot (i)(ii), cor:groupedknot, `CV.CarrierSlotFloor`; an RII move (G10). -/
theorem extreme_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ := by
  sorry

/-- **Row 177, R:extreme_selected** (R_EXTREME_SELECTED_COUPLE_PROOF.md).  Consumes: rows 168, 171,
CV:selector_A, CV:lem:homflyrows (ii)(iii), knot parity, turnlift (ii), uniformrot, cor:groupedknot,
`CV.CarrierSlotFloor`; the matched switch + RIII (G11's `G11_Config`) and an RII (G10). -/
theorem extreme_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ := by
  sorry

/-- prop:chamberinv (ii) in the shape `ChamberInvII` (accepted row 147, `CV.chamberinv_ii`). PROVED. -/
theorem cvt_chamberInvII : ChamberInvII :=
  fun _ _ hn _ _ hP hQ h => (CV.chamberinv_ii hn hP hQ h).symm

/-- **The row-178 assembly, PROVED NOW as a conditional theorem**: `CV.hyp_R` from the four open rows in
their fixed shapes and the accepted rows 164, 167, 170-173, 147 (ii) (`A2_cvRNear_of_rows`,
`hyp_R_of_near_of_chamberinv`). -/
theorem cv_R_of_rows
    (h174 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ)
    (h175 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ)
    (h176 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ)
    (h177 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ) :
    CV.hyp_R :=
  hyp_R_of_near_of_chamberinv
    (A2_cvRNear_of_rows
      (fun _n _ hn E e f g h3 h4e h4f h4g hE => availability_zero_one hn E e f g h3 h4e h4f h4g hE)
      (fun _n _ hn E e f g h3 h4e h4f h4g hE => generic_selector hn E e f g h3 h4e h4f h4g hE)
      (fun _n _ hn E e f g h3 h4e h4f h4g hE => generic_transport hn E e f g h3 h4e h4f h4g hE)
      h174 h175 h176 h177)
    cvt_chamberInvII

/-- **Row 178, R:cv_theorem** (FIXED: `RProof.cv_R : CV.hyp_R`) — the one-line assembly. -/
theorem cv_R : CV.hyp_R :=
  cv_R_of_rows
    (fun _n _ hn E e f g h3 h4e h4f h4g hE => generic_selected hn E e f g h3 h4e h4f h4g hE)
    (fun _n _ hn E e f g h3 h4e h4f h4g hE => extreme_pair_zero hn E e f g h3 h4e h4f h4g hE)
    (fun _n _ hn E e f g h3 h4e h4f h4g hE => extreme_transport hn E e f g h3 h4e h4f h4g hE)
    (fun _n _ hn E e f g h3 h4e h4f h4g hE => extreme_selected hn E e f g h3 h4e h4f h4g hE)

end RProof

/-! ## 4. Row 183 Bridge:theorem — `Bridge.sm_R : SM.hyp_R` (FIXED), BRIDGE.md §3 (19)-(21) -/

namespace Bridge

/-- **Row 183, Bridge:theorem.** The displayed bridge theorem (19)-(21): the proved CV R theorem gives SM's
Hypothesis R through B1-B4 (`SM.sm_R_of_cv_R`, Bridge/SmR.lean, library, PROVED from accepted rows). -/
theorem sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R

end Bridge

/-! ## 5. Row 184 SM:corner_laws_and_soft — `SM.corner_laws_and_soft` (FIXED) -/

namespace SM

open WallGerm SoftDuplication

/-! ### 5.1 Assumed interfaces (TO BE UNIFIED WITH LANE CORNER (110, 112) AND THE COMPARISON ROWS
(127, 128)): the printed C statements in the shape of the accepted A rows with `cornerStateSum` for
`amplitude` (the accepted C rows use exactly this rendering). -/

/-- thm:C-S7 (sm-4:267-275): "At a simple vertex–edge wall at (M;a), of bigon or sliding type, with halves
λ₁, λ₂ and contact sign s = χ_{a,a+1,M}(P₋), C(P₊) − C(P₋) = s C(λ₁) C(λ₂)" (halves generic by
lem:children (ii)). -/
structure CS7Data : Prop where
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a),
    ∃ (h₁ : Generic (firstHalf w.center M a)) (h₂ : Generic (secondHalf w.center M a)),
    ∀ s t : w.SideParameter,
      cornerStateSum hn (w.sideTuple true t).property -
        cornerStateSum hn (w.sideTuple false s).property =
        (w.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn hc.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn hc.1).2.1 h₂)

/-- thm:C-soft (sm-4:984-992): "for all sufficiently small ε > 0, C(P_ε) = ((χ₋ + χ₊)/2) C(P)" (every
sector, zero-selector sectors included; `P_ε` generic by lem:soft-generic). -/
structure CSoftData : Prop where
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (cornerStateSum (by omega) hQ : ℚ) = softAmplitudeMultiplier P j q * (cornerStateSum hn hP : ℚ)

/-- cor:C-inherits (sm-6:313-319): "Under Hypothesis R, C satisfies every identity of cor:A-lawful on the
domains stated there, in particular the cusp law C(P_loop) − C(P_no) = −κ C(P(0)∖j)": `ALawfulData` with
`cornerStateSum` for `amplitude` (root independence has no C analogue, FR-FIN-3; the deletion of a simple
cusp wall is generic whenever it satisfies (G1), sm-6:335-359). -/
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
  cusp_law : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j),
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
  vertex_edge_law : CS7Data
  triple_law : hyp_R
  soft_theorem : CSoftData
  reversal_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    cornerStateSum hn ((generic_reversal P).mpr hP) = (-1) ^ n * cornerStateSum hn hP
  triangles : cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.1 = -1 ∧
    cornerStateSum (by norm_num) (star_generic_law le_rfl).1.2.2.2.2.1 = 1

/-! ### 5.2 The final statement -/

/-- **Row 184, SM:corner_laws_and_soft** (TARGETS.md "Exact final target"): "the corner state sum C of SM
def:C satisfies every wall law on the domains of SM cor:A-lawful, together with SM thm:C-soft in every soft
sector … the conjunction of these actual C identities, with their printed quantifiers, signs and domains".
Coverage, field by field: chamber constancy and silent-wall invariance; the flat deletion law; both bigon
branches and the sliding branch of the vertex–edge law; triple-wall invariance at every source simple
triple wall (the proved `hyp_R`, no R assumption retained); the full cusp jump on the source domain and
every other identity inherited with cor:A-lawful; the direct empty-cusp zero; the soft theorem in every
sector. -/
structure CornerLawsAndSoftData : Prop where
  chamber : CChamberData
  silent : CSilentData
  flat : CS3Data
  vertex_edge : CS7Data
  triple : hyp_R
  inherited : CInheritsData
  empty_cusp : CS5Data
  soft : CSoftData

/-- **The row-184 assembly, PROVED NOW as a conditional theorem** from the four accepted C rows, the
proved R/bridge theorem `Bridge.sm_R`, and the three pending SM rows in their interface shapes. -/
theorem corner_laws_and_soft_of (hS7 : CS7Data) (hsoft : CSoftData)
    (hinh : hyp_R → CInheritsData) : CornerLawsAndSoftData where
  chamber := prop_C_chamber
  silent := prop_C_silent
  flat := thm_C_S3
  vertex_edge := hS7
  triple := Bridge.sm_R
  inherited := hinh Bridge.sm_R
  empty_cusp := thm_C_S5
  soft := hsoft

/-- thm:C-S7 (row 110, lane corner) — placeholder for the sketch. -/
theorem thm_C_S7 : CS7Data := by sorry
/-- thm:C-soft (row 112, lane corner) — placeholder for the sketch. -/
theorem thm_C_soft : CSoftData := by sorry
/-- cor:C-inherits (row 128, comparison rows) — placeholder for the sketch; the printed "Under Hypothesis
R" is the explicit parameter (axiom-policy mode `explicit_parameter`). -/
theorem cor_C_inherits (_hR : hyp_R) : CInheritsData := by sorry

/-- **Row 184** (FIXED: `SM.corner_laws_and_soft`). -/
theorem corner_laws_and_soft : CornerLawsAndSoftData :=
  corner_laws_and_soft_of thm_C_S7 thm_C_soft cor_C_inherits

end SM
