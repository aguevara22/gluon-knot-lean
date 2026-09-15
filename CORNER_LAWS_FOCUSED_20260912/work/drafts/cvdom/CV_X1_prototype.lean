import SM.FlatCarriersDefs
import SM.CX1
import CV.Events
import CV.Rotation
import Bridge.B1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # CV-DOM prototype (Analyst B, 2026-09-14): the statement of CV:def:X1 under option (C)

Option (C) = "CV-native carrier layer over `CrossingGeometry` / `CV.Generic`".  The key
observation of ANALYSIS_B.md is that the layer already exists and is ACCEPTED: the def:flat-carriers
row (`SM.FlatCarriersDefs`, namespace `SM.GeoCarrier`, prefix `geo`) restates the accepted carrier
machinery word for word on `CrossingGeometry P` — `geoMarkList`, `geoMarkSuccessor`,
`geoSmoothingSuccessor`, `GeoComponent`, `geoOwner`, `geoCornerCount`, `geoCornerPolygon`,
`geoCarrierCrossings`, `GeoIndependent`, `geoCarrierSelector` — together with the agreement layer
`geo*_eq_generic` / `geoComponentEquivGeneric` on SM-generic polygons.  CV:def:interlace (accepted,
`CV.Events`) already defines `CV.Ind`, `CV.N`, `CV.U` on `CrossingGeometry`.  So every CV
carrier-dependent definition row can be STATED now on its printed binder (`hP : CV.Generic P`, or
`CrossingGeometry` where the source says "diagrammatic"), through `hP.crossingGeometry`, with no
change to any accepted declaration.  This file typechecks the statement of CV:def:X1 (and the
shape of `CV.hyp_R` and of the B4 agreement) with `sorry` only in the places that are separate
rows/gaps (lem:piececurve = Gap G4, the corner-polygon regularity on the CV locus, B4 itself).

Checked with: `cd work/lean && lake env lean ../drafts/cvdom/CV_X1_prototype.lean`. -/

namespace CV

open SM SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## CV:def:smoothing (d1:355) and CV:def:wind (d1:487) on the geometric domain

"the carriers of S" are the cycles of the reconnected successor: the accepted `GeoComponent`.
CV:def:wind is stated on `CV.Generic` as printed ("Let P be generic ... the generic binder is part
of this definition"); the weight is literally the accepted `cornerSelector` of the corner polygon. -/

section Wind
variable (hP : CrossingGeometry P) (S : Finset (Crossing P))

/-- def:wind: `wt(L)` = `+1` (all right), `(−1)^{c(L)}` (all left), `0` (mixed) — the accepted
`cornerSelector` read on the carrier's corner polygon (`SM.geoCarrierSelector`). -/
noncomputable def weight (q : GeoComponent hP S) : ℤ := geoCarrierSelector hP S q

/-- def:wind: `wind(S) = ∏_L wt(L)` over the carriers of `S`. -/
noncomputable def wind : ℤ := ∏ q : GeoComponent hP S, weight hP S q

/-- "uniform if all its corners turn the same way" (def:wind). -/
def CarrierUniform (q : GeoComponent hP S) : Prop :=
  ∃ τ : SignType, τ ≠ 0 ∧ ∀ k, turn (geoCornerPolygon hP S q) k = τ

end Wind

/-! ## CV:def:pieces (d1:514): residual pieces = connected components of `G_P[U(S)]` -/

section Pieces
variable (hP : CrossingGeometry P) (S : Finset (Crossing P))

/-- The induced interlacement graph on the undominated set `U(S)` (accepted `CV.U`). -/
abbrev residualGraph : SimpleGraph (↑(U hP S) : Set (Crossing P)) :=
  (geometricInterlacementGraph hP).induce (↑(U hP S) : Set (Crossing P))

/-- def:pieces: "the residual pieces of `S` are the connected components `H ∈ π₀(G_P[U(S)])`". -/
abbrev Piece := (residualGraph hP S).ConnectedComponent

noncomputable instance : Fintype (Piece hP S) := Fintype.ofFinite _

/-- The crossings (labels) of a piece. -/
noncomputable def pieceLabels (H : Piece hP S) : Finset (Crossing P) :=
  Finset.univ.filter fun c : Crossing P =>
    ∃ hc : c ∈ (↑(U hP S) : Set (Crossing P)), (residualGraph hP S).connectedComponentMk ⟨c, hc⟩ = H

/-- `w(H) = |H|` (def:piecediagram: "every crossing is positive, so its writhe is `w(H) = |H|`"). -/
noncomputable def pieceWrithe (H : Piece hP S) : ℤ := (pieceLabels hP S H).card

/-- "the residual pieces assigned to `L` by Lemma lem:carriers(iv)": the pieces both of whose
occurrences of every crossing lie on the carrier `L`. lem:carriers (iv) (row 136) is the theorem
that every piece is assigned to exactly one carrier. -/
noncomputable def piecesOn (q : GeoComponent hP S) : Finset (Piece hP S) :=
  Finset.univ.filter fun H : Piece hP S =>
    ∀ c ∈ pieceLabels hP S H, ∀ v : Visit P, v.1 = c → geoOwner hP S (Sum.inr v) = q

end Pieces

/-! ## CV:lem:piececurve (d1:592, row 143, Gap G4) and CV:def:piecediagram (d1:565, row 142)

The piece curve `C_H` is the carrier of `S ∪ K_H` that carries `H`, for the greedy independent
set `K_H` of Step 5 of the printed proof; its positive lift is the diagram of the piece and `P_H`
its HOMFLY–PT polynomial.  Both are separate rows; here only their TYPES are fixed (bodies `sorry`),
so that def:X1 can be stated on top of them exactly as printed. -/

section PieceCurve
variable (hG : CV.Generic P) (S : Finset (Crossing P))

/-- Step 5 of lem:piececurve: the crossings smoothed in addition to `S` to isolate `H` (Gap G4). -/
noncomputable def pieceSupport (H : Piece hG.crossingGeometry S) : Finset (Crossing P) := sorry

/-- The carrier of `S ∪ K_H` carrying `H` (lem:carriers (iv) at `S ∪ K_H`). -/
noncomputable def pieceCarrier (H : Piece hG.crossingGeometry S) :
    GeoComponent hG.crossingGeometry (S ∪ pieceSupport hG S H) := sorry

/-- lem:selectorid (A) / lem:carriers (ii) on the CV locus: every carrier has ≥ 3 corners
(row 164 `CV:selector_A`; a theorem of the geometric tier, see ANALYSIS_B.md unit C2). -/
theorem three_le_geoCornerCount (S' : Finset (Crossing P)) (q : GeoComponent hG.crossingGeometry S') :
    3 ≤ geoCornerCount hG.crossingGeometry S' q := sorry

/-- The corner polygon of a carrier of a CV-generic polygon is a CV-regular polygon
(def:wind: "under genericity [the turn] is nonzero"; unit C2). -/
theorem geoCornerPolygon_cvRegular (S' : Finset (Crossing P)) (q : GeoComponent hG.crossingGeometry S') :
    CV.Regular (geoCornerPolygon hG.crossingGeometry S' q) := sorry

/-- The genericity of the one-component shadow of a carrier's corner polygon
(the CV-locus analogue of `SM.Link.carrierShadow_generic`; unit C2). -/
theorem carrierShadow_generic (S' : Finset (Crossing P)) (q : GeoComponent hG.crossingGeometry S') :
    (Shadow.single ⟨geoCornerCount hG.crossingGeometry S' q, three_le_geoCornerCount hG S' q,
      geoCornerPolygon hG.crossingGeometry S' q⟩).Generic := sorry

/-- def:piecediagram: the diagram of the piece `H` — the positive lift ("divide convention") of the
piece curve `C_H`. -/
noncomputable def pieceDiagram (H : Piece hG.crossingGeometry S) : Diagram :=
  (Shadow.single ⟨_, three_le_geoCornerCount hG _ (pieceCarrier hG S H),
    geoCornerPolygon hG.crossingGeometry _ (pieceCarrier hG S H)⟩).positiveDiagram
    (carrierShadow_generic hG _ (pieceCarrier hG S H))

/-- `P_H`, "the HOMFLY–PT polynomial of the link that the piece `H` presents". -/
noncomputable def piecePolynomial (H : Piece hG.crossingGeometry S) : R :=
  homfly (pieceDiagram hG S H)

end PieceCurve

/-! ## CV:def:X1 (d1_setup.tex:908–930), stated on the PRINTED binder `hP : CV.Generic P` -/

section X1
variable (hG : CV.Generic P) (S : Finset (Crossing P))

/-- `P_{S,L} = ∏_{H carried by L} P_H` (empty product `1`). -/
noncomputable def groupedPoly (q : GeoComponent hG.crossingGeometry S) : R :=
  ∏ H ∈ piecesOn hG.crossingGeometry S q, piecePolynomial hG S H

/-- `w_{S,L} = Σ_{H carried by L} w(H)` (empty sum `0`). -/
noncomputable def groupedWrithe (q : GeoComponent hG.crossingGeometry S) : ℤ :=
  ∑ H ∈ piecesOn hG.crossingGeometry S q, pieceWrithe hG.crossingGeometry S H

/-- `R(L) = |rot(L)|` with CV def:rot (accepted `CV.rotAbs`) on the carrier's corner polygon. -/
noncomputable def carrierR (q : GeoComponent hG.crossingGeometry S) : ℕ :=
  CV.rotAbs (geoCornerPolygon hG.crossingGeometry S q) (geoCornerPolygon_cvRegular hG S q)

/-- "The slot of `L` is the integer `1 − w_{S,L} − R(L)`". -/
noncomputable def slot (q : GeoComponent hG.crossingGeometry S) : ℤ :=
  1 - groupedWrithe hG S q - (carrierR hG S q : ℤ)

/-- "the factor `Ω₁(S,L) = [a^{1−w_{S,L}−R(L)} z⁰] P_{S,L}(a,z)` — the coefficient itself, taken as a
value, with no sign gate and no zero-gate applied". -/
noncomputable def Omega1 (q : GeoComponent hG.crossingGeometry S) : ℤ :=
  coeffAt (slot hG S q) 0 (groupedPoly hG S q)

end X1

/-- **CV:def:X1.** `X₁(P) = Σ_{S ∈ Ind(G_P)} wind(S) ∏_L Ω₁(S,L)`, "the inner product running over the
`|S|+1` carriers of `S`" (the carriers form the `Fintype` `GeoComponent`; that there are `|S|+1` of
them is lem:carriers (i)).  Binder: `hG : CV.Generic P` — the printed "Let `P` be generic". -/
noncomputable def X1 (_hn : 3 ≤ n) (P : LabelledTuple n) (hG : CV.Generic P) : ℤ :=
  ∑ S ∈ Ind hG.crossingGeometry,
    wind hG.crossingGeometry S * ∏ q : GeoComponent hG.crossingGeometry S, Omega1 hG S q

/-- The DEFINE-row bundle for CV:def:X1 (one field per printed sentence), as it would be reviewed. -/
structure X1DefinitionData : Prop where
  /-- "with the empty product `P_{S,L} = 1` and the empty sum `w_{S,L} = 0` when no piece is carried" -/
  empty_conventions : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hG : CV.Generic P)
    (S : Finset (Crossing P)) (q : GeoComponent hG.crossingGeometry S),
    piecesOn hG.crossingGeometry S q = ∅ → groupedPoly hG S q = 1 ∧ groupedWrithe hG S q = 0
  /-- the slot and the factor, as displayed -/
  factor : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hG : CV.Generic P)
    (S : Finset (Crossing P)) (q : GeoComponent hG.crossingGeometry S),
    Omega1 hG S q = coeffAt (1 - groupedWrithe hG S q - (carrierR hG S q : ℤ)) 0 (groupedPoly hG S q)
  /-- the state sum, as displayed, the sum over `Ind(G_P)` of CV:def:interlace -/
  state_sum : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hG : CV.Generic P),
    X1 hn P hG = ∑ S ∈ Ind hG.crossingGeometry,
      wind hG.crossingGeometry S * ∏ q : GeoComponent hG.crossingGeometry S, Omega1 hG S q
  /-- def:wind's last sentence: `wind(S) ≠ 0` forces every carrier of `S` to be uniform -/
  wind_ne_zero : ∀ (n : ℕ) [NeZero n] (P : LabelledTuple n) (hG : CV.Generic P)
    (S : Finset (Crossing P)), wind hG.crossingGeometry S ≠ 0 →
      ∀ q : GeoComponent hG.crossingGeometry S, CarrierUniform hG.crossingGeometry S q

theorem X1_definition : X1DefinitionData where
  empty_conventions := fun _ _ _ _ _ _ h => by
    simp [groupedPoly, groupedWrithe, h]
  factor := fun _ _ _ _ _ _ => rfl
  state_sum := fun _ _ _ _ _ => rfl
  wind_ne_zero := by
    intro n _ P hG S hw q
    have hq : weight hG.crossingGeometry S q ≠ 0 := by
      intro h0
      apply hw
      exact Finset.prod_eq_zero (Finset.mem_univ q) h0
    unfold weight geoCarrierSelector cornerSelector at hq
    by_cases hr : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = -1
    · exact ⟨-1, by decide, hr⟩
    · by_cases hl : ∀ k, turn (geoCornerPolygon hG.crossingGeometry S q) k = 1
      · exact ⟨1, by decide, hl⟩
      · exact absurd (by simp [hr, hl]) hq

/-! ## Where `X₁` is EVALUATED in the final proof, and the two agreement statements

`Bridge.sm_R` applies `RProof.cv_R : CV.hyp_R` to the event `Bridge.eventOfTriple hn g h` of an SM
simple triple germ `g`; the two side values are `X1` at `E.curve t`, `t ≠ 0`, and these polygons
are SM-generic (`g.generic_punctured`).  So `Bridge.B4` is only ever invoked on SM-generic polygons,
where the geo layer agrees with the accepted lane (`geoComponentEquivGeneric`, ...). -/

/-- Every polygon at which `Bridge.sm_R` evaluates `X₁` is SM-generic. -/
theorem eventOfTriple_sides_sm_generic (hn : 3 ≤ n) (g : WallGerm n) {e f k : ZMod n}
    (h : g.TripleAt e f k) (t : (Bridge.eventOfTriple hn g h).Parameter) (ht : t.val ≠ 0) :
    SM.Generic ((Bridge.eventOfTriple hn g h).curve t) :=
  g.generic_punctured t ht

/-- Bridge B4 (row 182), shape: on an SM-generic polygon the CV state sum equals the accepted
corner state sum `C(P)` (through `generic_of_sm`, `geoComponentEquivGeneric`, lem:C-X1 = `SM.C_X1`
and cb:products; see ANALYSIS_B.md unit C5). -/
theorem X1_eq_cornerStateSum (hn : 3 ≤ n) (hP : SM.Generic P) :
    X1 hn P (generic_of_sm hn hP) = cornerStateSum hn hP := sorry

/-- CV:ax:R (row `CV:ax:R`, fixed name `CV.hyp_R` — this prototype uses a primed name so as not to
pre-empt the row): the printed statement on the printed domain, with the sides read as point values
on a punctured neighbourhood (chamber values by prop:chamberinv (ii) / def:event). -/
def hyp_R' : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ rep e < rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ rep e < rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0),
      tp.val < δ → -δ < tm.val →
      X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
        X1 hn (E.curve tm) (E.generic_punctured tm hm.ne)

end CV
