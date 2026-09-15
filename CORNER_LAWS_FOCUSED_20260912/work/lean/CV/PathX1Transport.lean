import CV.ChamberInvII
import CV.PieceHomflyTransport


/-! Ported 2026-09-14 07:16Z from work/drafts/cvdom/U5b/CVPathX1Transport.lean (CV-DOM unit U5b, report work/drafts/cvdom/U5b/REPORT.md): library: the ChamberInvII + PieceHomflyTransport chain re-bound to an arbitrary tier-2 path datum (X1_eq_of_geoWeakPathData, X1_eq_of_weakGeneric_path / _family). Only this header added. -/
/-! # CV/PathX1Transport — `X₁` is carried along any path of weakly generic polygons
(CV-DOM unit U5b, part 1; library module, no row)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3, §5 row **U5b**, §6 item 7). Draft home
work/drafts/cvdom/U5b/; intended home `work/lean/CV/PathX1Transport.lean`. Nothing under work/lean was written.

## Content

CV/ChamberInvII.lean and CV/PieceHomflyTransport.lean carry every ingredient of `X₁` (CV:def:X1, row 146) —
the independent sets `Ind`, the pieces, `wind`, the carriers' rotations `R(L)`, the piece polynomials `P_H` —
between two CV-generic polygons `P`, `Q` **of one CV chamber**; the chamber enters only through the tier-2 path
datum `chamber_geoWeakPathData hn hP hQ h : GeoWeakPathData hn (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ) hs`
(SM/GeoPathTransport.lean, U5a) that the generic path of chamberinv (i) supplies. A silent wall lies inside no
chamber (rem:silencenew, d1_setup.tex:1420–1428: "a silent wall *is* a wall … so chamber constancy does not
cross it"), so lem:silence needs the same chain with the datum taken as a **hypothesis**: a path of *weakly*
generic polygons (`SM.WeakGeneric`, the accepted tier 2) between two CV-generic ends, which may pass through
non-generic polygons — the printed proof "is the path argument of Proposition prop:chamberinv (ii) run through
the wall, and it is printed rather than cited because a silent wall lies inside no chamber" (d1:1394–1397).

This module is that re-binding: every lemma of ChamberInvII §3–§7 and PieceHomflyTransport §2 restated on
`d : GeoWeakPathData hn (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ) hs` (suffix `_of_pathData`), then

* `CV.X1_eq_of_geoWeakPathData hn hP hQ d : X1 hn Q hQ = X1 hn P hP`;
* `CV.X1_eq_of_weakGeneric_path hn hP hQ (γ : Path P Q) (hW : ∀ t, WeakGeneric (γ t))`;
* `CV.X1_eq_of_weakGeneric_family hn γ hγc hW hP hQ : X1 hn (γ 1) hQ = X1 hn (γ 0) hP`.

The proofs are those of ChamberInvII / PieceHomflyTransport with `chamber_geoWeakPathData hn hP hQ h` replaced
by `d`, `crossing_iff_of_mem_chamber hn hP hQ h` by `hs`, `geoMarkTransport_of_mem_chamber hn hP hQ h` by
`d.transport`. The chamber versions are the special case `d := chamber_geoWeakPathData hn hP hQ h`
(`X1_eq_of_mem_chamber'` at the end, a cross-check against the accepted `chamberinv_ii`).

`hn : 3 ≤ n` is carried as `X₁` carries it (reading (iii), DECISION_FINAL §2). Axioms: standard plus
`SM.lit_homfly` (through `homfly`, the polynomial `X₁` reads) on the HOMFLY-dependent declarations. -/

namespace CV

open SM SM.GeoCarrier SM.Carrier SM.Link

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

/-! ## 1. The datum, the transport, records, turns, independent sets -/

section PathData

variable (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s}
  (d : GeoWeakPathData hn (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ) hs)
include d

/-- The mark transport of the path datum (marks, interlacement, signs), on the row binders
(`hP.crossingGeometry`, `hQ.crossingGeometry`; the tier-1 proofs of `d` are identified by proof irrelevance). -/
theorem geoMarkTransport_of_pathData : GeoMarkTransport hP.crossingGeometry hQ.crossingGeometry hs :=
  d.transport

/-- Vertex turn signs are constant along the path. -/
theorem turn_eq_of_pathData (i : ZMod n) : turn Q i = turn P i := d.turn_eq i

/-- The same-edge crossing-parameter order is constant along the path. -/
theorem crossingParameterOrderAgrees_of_pathData : CrossingParameterOrderAgrees P Q := d.order_agrees

/-- Crossing signs are constant along the path. -/
theorem crossingSign_eq_of_pathData (i j : ZMod n) (hij : IsCrossing P {i, j}) :
    crossingSign Q i j = crossingSign P i j :=
  d.transport.sign_eq i j hij

/-- **The complete geometric records agree along the path** (`GeometricRecordsAgree`: crossing supports,
Gauss list and word, interlacement, signs). -/
theorem geometricRecordsAgree_of_pathData :
    GeometricRecordsAgree hP.crossingGeometry hQ.crossingGeometry :=
  d.recordsAgree

/-- Interlacement is constant along the path. -/
theorem geometricInterlaces_iff_of_pathData (x y : Crossing P) :
    GeometricInterlaces hP.crossingGeometry x y ↔
      GeometricInterlaces hQ.crossingGeometry (crossingTransport hs x) (crossingTransport hs y) :=
  (geoMarkTransport_of_pathData hn hP hQ d).interlaces_iff x y

/-- `Ind(G_P)` is carried onto `Ind(G_Q)` (CV:def:interlace, `CV.Ind`). -/
theorem mem_Ind_transport_iff_of_pathData (S : Finset (Crossing P)) :
    transportSupport hs S ∈ Ind hQ.crossingGeometry ↔ S ∈ Ind hP.crossingGeometry := by
  rw [mem_Ind_iff_geoIndependent, mem_Ind_iff_geoIndependent]
  exact (geoMarkTransport_of_pathData hn hP hQ d).geoIndependent_iff S

/-- `Ind(G_Q)` is the image of `Ind(G_P)` under the support bijection (the reindexing of the `X1` sum). -/
theorem Ind_eq_map_of_pathData :
    Ind hQ.crossingGeometry =
      (Ind hP.crossingGeometry).map (GeoMarkTransport.supportEquiv hs).toEmbedding := by
  ext S'
  rw [Finset.mem_map_equiv]
  obtain ⟨S, rfl⟩ := GeoMarkTransport.support_surjective (hs := hs) S'
  rw [← GeoMarkTransport.supportEquiv_apply, Equiv.symm_apply_apply, GeoMarkTransport.supportEquiv_apply,
    mem_Ind_transport_iff_of_pathData hn hP hQ d S]

/-- The neighbourhood `N(S)` is carried. -/
theorem mem_N_transport_iff_of_pathData (S : Finset (Crossing P)) (y : Crossing P) :
    crossingTransport hs y ∈ N hQ.crossingGeometry (transportSupport hs S) ↔ y ∈ N hP.crossingGeometry S := by
  rw [mem_N_iff, mem_N_iff]
  constructor
  · rintro ⟨x', hx', hI⟩
    obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
    rw [GeoMarkTransport.mem_support] at hx'
    exact ⟨x, hx', (geometricInterlaces_iff_of_pathData hn hP hQ d y x).mpr hI⟩
  · rintro ⟨x, hx, hI⟩
    exact ⟨crossingTransport hs x, (GeoMarkTransport.mem_support S x).mpr hx,
      (geometricInterlaces_iff_of_pathData hn hP hQ d y x).mp hI⟩

theorem N_transport_of_pathData (S : Finset (Crossing P)) :
    N hQ.crossingGeometry (transportSupport hs S) = transportSupport hs (N hP.crossingGeometry S) := by
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [mem_N_transport_iff_of_pathData hn hP hQ d S y, GeoMarkTransport.mem_support]

/-- The unselected complement `U(S)` is carried. -/
theorem mem_U_transport_iff_of_pathData (S : Finset (Crossing P)) (y : Crossing P) :
    crossingTransport hs y ∈ U hQ.crossingGeometry (transportSupport hs S) ↔ y ∈ U hP.crossingGeometry S := by
  rw [mem_U, mem_U, GeoMarkTransport.mem_support, mem_N_transport_iff_of_pathData hn hP hQ d S y]

theorem U_transport_of_pathData (S : Finset (Crossing P)) :
    U hQ.crossingGeometry (transportSupport hs S) = transportSupport hs (U hP.crossingGeometry S) := by
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [mem_U_transport_iff_of_pathData hn hP hQ d S y, GeoMarkTransport.mem_support]

/-! ## 2. def:wind, rotations and positive lifts along the path -/

variable (S : Finset (Crossing P))

/-- CV:def:wind's weight of a carrier is constant along the path (`weight = geoCarrierSelector`). -/
theorem weight_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    weight hQ.crossingGeometry (transportSupport hs S) ((geoMarkTransport_of_pathData hn hP hQ d).component S q) =
      weight hP.crossingGeometry S q :=
  d.geoCarrierSelector_eq hn ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- **CV:def:wind's `wind(S)` is constant along the path.** -/
theorem wind_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry) :
    wind hQ.crossingGeometry (transportSupport hs S) = wind hP.crossingGeometry S :=
  d.geoWind_eq hn ((mem_Ind_iff_geoIndependent _ S).mp hS)

/-- Uniformity of a carrier is constant along the path. -/
theorem carrierUniform_iff_of_pathData (hS : S ∈ Ind hP.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    CarrierUniform hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q) ↔
      CarrierUniform hP.crossingGeometry S q :=
  d.geoCarrierUniform_iff hn ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- The corner turns of a carrier are constant along the path (at the cast index). -/
theorem turn_geoCornerPolygon_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S)
    (j : ZMod (geoCornerCount hQ.crossingGeometry (transportSupport hs S)
      ((geoMarkTransport_of_pathData hn hP hQ d).component S q))) :
    turn (geoCornerPolygon hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q)) j =
      turn (geoCornerPolygon hP.crossingGeometry S q)
        (Equiv.cast (congrArg ZMod ((geoMarkTransport_of_pathData hn hP hQ d).geoCornerCount_eq S q)) j) :=
  d.turn_geoCornerPolygon_eq hn ((mem_Ind_iff_geoIndependent _ S).mp hS) q j

/-- **The rotation of a carrier's corner polygon is constant along the path** (lem:rot (ii); CV:def:rot's
`R(L)` is a function of it). -/
theorem geoCarrierRotation_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    geoCarrierRotation hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q) =
      geoCarrierRotation hP.crossingGeometry S q :=
  d.rotation_eq' ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- The same for the rotation number of the corner polygon itself. -/
theorem rotationNumber_geoCornerPolygon_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    rotationNumber (geoCornerPolygon hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q)) =
      rotationNumber (geoCornerPolygon hP.crossingGeometry S q) :=
  geoCarrierRotation_eq_of_pathData hn hP hQ d S hS q

theorem geoCarrierRotationInt_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    geoCarrierRotationInt hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q) =
      geoCarrierRotationInt hP.crossingGeometry S q :=
  d.rotationInt_eq ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- **The HOMFLY polynomial of the positive lift of a carrier is constant along the path** (lit:homfly's
planar clause along the path, the `homfly_eq` clause of `d`). -/
theorem homfly_geoPositiveLift_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : GeoIndependent (CarrierGeometry.ofCV hQ).cg (transportSupport hs S))
    (q : GeoComponent hP.crossingGeometry S) :
    homfly (geoPositiveLift hn (CarrierGeometry.ofCV hQ) hS'
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q)) =
      homfly (geoPositiveLift hn (CarrierGeometry.ofCV hP) ((mem_Ind_iff_geoIndependent _ S).mp hS) q) :=
  d.homfly_eq' ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- The retained crossings of a carrier are carried. -/
theorem geoCarrierCrossings_eq_of_pathData (q : GeoComponent hP.crossingGeometry S) :
    geoCarrierCrossings hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q) =
      (geoCarrierCrossings hP.crossingGeometry S q).map (crossingTransport hs).toEmbedding :=
  (geoMarkTransport_of_pathData hn hP hQ d).geoCarrierCrossings_eq S q

theorem card_geoCarrierCrossings_eq_of_pathData (q : GeoComponent hP.crossingGeometry S) :
    (geoCarrierCrossings hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q)).card =
      (geoCarrierCrossings hP.crossingGeometry S q).card :=
  (geoMarkTransport_of_pathData hn hP hQ d).card_geoCarrierCrossings_eq S q

/-! ## 3. Pieces along the path -/

/-- The canonical identification restricts to a bijection `U(S) → U(S')`. -/
theorem bijOn_U_of_pathData :
    Set.BijOn (crossingTransport hs) (↑(U hP.crossingGeometry S) : Set (Crossing P))
      (↑(U hQ.crossingGeometry (transportSupport hs S)) : Set (Crossing Q)) :=
  (crossingTransport _).bijOn fun y => by
    simp only [Finset.mem_coe]
    exact mem_U_transport_iff_of_pathData hn hP hQ d S y

/-- The residual graphs `G_P[U(S)]` and `G_Q[U(S')]` are isomorphic. -/
noncomputable def residualIso_of_pathData :
    residualGraph hP.crossingGeometry S ≃g residualGraph hQ.crossingGeometry (transportSupport hs S) :=
  SimpleGraph.Iso.induce (geoMarkTransport_of_pathData hn hP hQ d).interlacementIso
    (bijOn_U_of_pathData hn hP hQ d S)

/-- **The pieces of `S` correspond to the pieces of `S'`** (CV:def:pieces). -/
noncomputable def pieceEquiv_of_pathData :
    Piece hP.crossingGeometry S ≃ Piece hQ.crossingGeometry (transportSupport hs S) :=
  (residualIso_of_pathData hn hP hQ d S).connectedComponentEquiv

theorem pieceEquiv_of_pathData_pieceOf (c : Crossing P) (hc : c ∈ U hP.crossingGeometry S) :
    pieceEquiv_of_pathData hn hP hQ d S (pieceOf hP.crossingGeometry S c hc) =
      pieceOf hQ.crossingGeometry (transportSupport hs S) (crossingTransport hs c)
        ((mem_U_transport_iff_of_pathData hn hP hQ d S c).mpr hc) := by
  unfold pieceEquiv_of_pathData pieceOf
  rw [SimpleGraph.Iso.connectedComponentEquiv_apply, SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- The labels of a piece are carried. -/
theorem pieceLabels_eq_of_pathData (H : Piece hP.crossingGeometry S) :
    pieceLabels hQ.crossingGeometry (transportSupport hs S) (pieceEquiv_of_pathData hn hP hQ d S H) =
      (pieceLabels hP.crossingGeometry S H).map (crossingTransport hs).toEmbedding := by
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_pieceLabels, mem_pieceLabels]
  constructor
  · rintro ⟨hc', hH⟩
    have hc : c ∈ U hP.crossingGeometry S := (mem_U_transport_iff_of_pathData hn hP hQ d S c).mp hc'
    refine ⟨hc, (pieceEquiv_of_pathData hn hP hQ d S).injective ?_⟩
    rw [pieceEquiv_of_pathData_pieceOf]
    exact hH
  · rintro ⟨hc, hH⟩
    refine ⟨(mem_U_transport_iff_of_pathData hn hP hQ d S c).mpr hc, ?_⟩
    rw [← pieceEquiv_of_pathData_pieceOf hn hP hQ d S c hc, hH]

/-- The writhe `w(H) = |H|` of a piece is carried. -/
theorem pieceWrithe_eq_of_pathData (H : Piece hP.crossingGeometry S) :
    pieceWrithe hQ.crossingGeometry (transportSupport hs S) (pieceEquiv_of_pathData hn hP hQ d S H) =
      pieceWrithe hP.crossingGeometry S H := by
  unfold pieceWrithe
  rw [pieceLabels_eq_of_pathData, Finset.card_map]

/-- The pieces assigned to a carrier are carried onto the pieces assigned to its copy. -/
theorem mem_piecesOn_transport_iff_of_pathData (q : GeoComponent hP.crossingGeometry S)
    (H : Piece hP.crossingGeometry S) :
    pieceEquiv_of_pathData hn hP hQ d S H ∈
        piecesOn hQ.crossingGeometry (transportSupport hs S)
          ((geoMarkTransport_of_pathData hn hP hQ d).component S q) ↔
      H ∈ piecesOn hP.crossingGeometry S q := by
  rw [mem_piecesOn, mem_piecesOn, pieceLabels_eq_of_pathData]
  constructor
  · intro hall c hc v hv
    have := hall (crossingTransport hs c) (Finset.mem_map_of_mem _ hc)
      (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, (geoMarkTransport_of_pathData hn hP hQ d).owner_transport] at this
    exact ((geoMarkTransport_of_pathData hn hP hQ d).component S).injective this
  · intro hall c' hc' w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hc'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hv : v.1 = c := (crossingTransport hs).injective hw
    rw [← markTransport_visit, GeoMarkTransport.owner_transport, hall c hc v hv]

theorem piecesOn_transport_eq_of_pathData (q : GeoComponent hP.crossingGeometry S) :
    piecesOn hQ.crossingGeometry (transportSupport hs S)
        ((geoMarkTransport_of_pathData hn hP hQ d).component S q) =
      (piecesOn hP.crossingGeometry S q).map (pieceEquiv_of_pathData hn hP hQ d S).toEmbedding := by
  ext H'
  obtain ⟨H, rfl⟩ := (pieceEquiv_of_pathData hn hP hQ d S).surjective H'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_piecesOn_transport_iff_of_pathData]

/-! ## 4. The piece polynomials along the path (PieceHomflyTransport §2 re-bound) -/

/-- **The piece polynomials are carried along the path**: at `Q` the carrier of `S' ∪ K'` (the support chosen
at `Q`) and the transport of the carrier of `S ∪ K_H` (the support chosen at `P`) both carry exactly the labels
of the piece, so their positive lifts have the same HOMFLY polynomial
(`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`, CV:lem:pieceintrinsic + CV:ax:gausscode), and the
transported lift has the polynomial of the lift at `P` (`homfly_geoPositiveLift_eq_of_pathData`). -/
theorem pieceHomfly_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport hs S ∈ Ind hQ.crossingGeometry) (H : Piece hP.crossingGeometry S) :
    pieceHomfly hn (hQ.diagrammatic hn) hS' (pieceEquiv_of_pathData hn hP hQ d S H) =
      pieceHomfly hn (hP.diagrammatic hn) hS H := by
  have hSK : S ∪ pieceSupport (hP.diagrammatic hn) hS H ∈ Ind hP.crossingGeometry :=
    pieceSupport_mem_Ind (hP.diagrammatic hn) hS H
  have hSK' : transportSupport hs (S ∪ pieceSupport (hP.diagrammatic hn) hS H) ∈ Ind hQ.crossingGeometry :=
    (mem_Ind_transport_iff_of_pathData hn hP hQ d _).mpr hSK
  have hK2 : GeoIndependent (CarrierGeometry.ofCV hQ).cg
      (transportSupport hs (S ∪ pieceSupport (hP.diagrammatic hn) hS H)) :=
    geoIndependent_of_mem_Ind _ hSK'
  have hcross : geoCarrierCrossings hQ.crossingGeometry
      (transportSupport hs S ∪ pieceSupport (hQ.diagrammatic hn) hS' (pieceEquiv_of_pathData hn hP hQ d S H))
      (pieceCarrier (hQ.diagrammatic hn) hS' (pieceEquiv_of_pathData hn hP hQ d S H)) =
      geoCarrierCrossings hQ.crossingGeometry
        (transportSupport hs (S ∪ pieceSupport (hP.diagrammatic hn) hS H))
        ((geoMarkTransport_of_pathData hn hP hQ d).component _ (pieceCarrier (hP.diagrammatic hn) hS H)) := by
    rw [pieceCarrier_geoCarrierCrossings, pieceLabels_eq_of_pathData hn hP hQ d S H,
      geoCarrierCrossings_eq_of_pathData hn hP hQ d, pieceCarrier_geoCarrierCrossings]
  unfold pieceHomfly pieceDiagram
  rw [homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic (hQ.diagrammatic hn))
    (pieceSupport_geoIndependent (hQ.diagrammatic hn) hS' (pieceEquiv_of_pathData hn hP hQ d S H)) hK2
    (pieceCarrier (hQ.diagrammatic hn) hS' (pieceEquiv_of_pathData hn hP hQ d S H)) _ hcross]
  exact homfly_geoPositiveLift_eq_of_pathData hn hP hQ d _ hSK hK2 (pieceCarrier (hP.diagrammatic hn) hS H)

/-! ## 5. `X₁` along the path (ChamberInvII §7 re-bound) -/

/-- `w_{S,L}` is carried. -/
theorem groupedWrithe_eq_of_pathData (q : GeoComponent hP.crossingGeometry S) :
    groupedWrithe hQ ((geoMarkTransport_of_pathData hn hP hQ d).component S q) = groupedWrithe hP q := by
  unfold groupedWrithe
  rw [piecesOn_transport_eq_of_pathData hn hP hQ d S q, Finset.sum_map]
  exact Finset.sum_congr rfl fun H _ => pieceWrithe_eq_of_pathData hn hP hQ d S H

/-- `R(L) = |rot(L)|` is carried. -/
theorem carrierR_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport hs S ∈ Ind hQ.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    carrierR hn hQ hS' ((geoMarkTransport_of_pathData hn hP hQ d).component S q) = carrierR hn hP hS q := by
  unfold carrierR rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [rot_eq_rotationNumber, rot_eq_rotationNumber]
  exact rotationNumber_geoCornerPolygon_eq_of_pathData hn hP hQ d S hS q

/-- `P_{S,L}` is carried. -/
theorem groupedPoly_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport hs S ∈ Ind hQ.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    groupedPoly hn hQ hS' ((geoMarkTransport_of_pathData hn hP hQ d).component S q) = groupedPoly hn hP hS q := by
  unfold groupedPoly
  rw [piecesOn_transport_eq_of_pathData hn hP hQ d S q, Finset.prod_map]
  exact Finset.prod_congr rfl fun H _ => pieceHomfly_eq_of_pathData hn hP hQ d S hS hS' H

/-- The slot `1 − w_{S,L} − R(L)` is carried. -/
theorem slot_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport hs S ∈ Ind hQ.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    slot hn hQ hS' ((geoMarkTransport_of_pathData hn hP hQ d).component S q) = slot hn hP hS q := by
  unfold slot
  rw [groupedWrithe_eq_of_pathData hn hP hQ d S q, carrierR_eq_of_pathData hn hP hQ d S hS hS' q]

/-- The factor `Ω₁(S,L)` is carried. -/
theorem Omega1_eq_of_pathData (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport hs S ∈ Ind hQ.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    Omega1 hn hQ hS' ((geoMarkTransport_of_pathData hn hP hQ d).component S q) = Omega1 hn hP hS q := by
  unfold Omega1
  rw [slot_eq_of_pathData hn hP hQ d S hS hS' q, groupedPoly_eq_of_pathData hn hP hQ d S hS hS' q]

/-- The summand of `X₁` (the total function `X1Summand` of CV/ChamberInvII.lean) is carried. -/
theorem X1Summand_eq_of_pathData :
    X1Summand hn hQ (transportSupport hs S) = X1Summand hn hP S := by
  unfold X1Summand
  by_cases hS : S ∈ Ind hP.crossingGeometry
  · have hS' : transportSupport hs S ∈ Ind hQ.crossingGeometry :=
      (mem_Ind_transport_iff_of_pathData hn hP hQ d S).mpr hS
    rw [dite_eq_left hS, dite_eq_left hS', wind_eq_of_pathData hn hP hQ d S hS]
    congr 1
    exact (Fintype.prod_equiv ((geoMarkTransport_of_pathData hn hP hQ d).component S) _ _
      fun q => (Omega1_eq_of_pathData hn hP hQ d S hS hS' q).symm).symm
  · have hS' : transportSupport hs S ∉ Ind hQ.crossingGeometry :=
      fun h' => hS ((mem_Ind_transport_iff_of_pathData hn hP hQ d S).mp h')
    rw [dite_eq_right hS, dite_eq_right hS']

end PathData

/-! ## 6. The path theorems -/

/-- **`X₁` is carried by a tier-2 path datum between two CV-generic polygons**: the sum over `Ind(G_Q)` is
reindexed along the support bijection (`Ind_eq_map_of_pathData`), `wind` by `wind_eq_of_pathData`, the product
over carriers along `d.transport.component S`, and each `Ω₁` by `Omega1_eq_of_pathData`. -/
theorem X1_eq_of_geoWeakPathData (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s}
    (d : GeoWeakPathData hn (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ) hs) :
    X1 hn Q hQ = X1 hn P hP := by
  rw [X1_eq_sum_X1Summand hn hQ, X1_eq_sum_X1Summand hn hP, Ind_eq_map_of_pathData hn hP hQ d, Finset.sum_map]
  exact Finset.sum_congr rfl fun S _ => X1Summand_eq_of_pathData hn hP hQ d S

/-- **`X₁` is constant along a path of weakly generic polygons between two CV-generic polygons** (the path may
pass through non-generic, weakly generic polygons — e.g. the centre of a silent event). -/
theorem X1_eq_of_weakGeneric_path (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (γ : Path P Q)
    (hW : ∀ t, WeakGeneric (γ t)) : X1 hn Q hQ = X1 hn P hP := by
  obtain ⟨hs, d⟩ := GeoWeakPathData.of_path hn γ hW (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ)
  exact X1_eq_of_geoWeakPathData hn hP hQ d

/-- The same for a continuous family `unitInterval → (ℝ²)^n` of weakly generic polygons whose ends are
CV-generic. -/
theorem X1_eq_of_weakGeneric_family (hn : 3 ≤ n) (γ : unitInterval → LabelledTuple n) (hγc : Continuous γ)
    (hW : ∀ t, WeakGeneric (γ t)) (hP : Generic (γ 0)) (hQ : Generic (γ 1)) :
    X1 hn (γ 1) hQ = X1 hn (γ 0) hP :=
  X1_eq_of_geoWeakPathData hn hP hQ (GeoWeakPathData.of_family hn γ hγc hW)

/-- Cross-check: the chamber case is the datum `chamber_geoWeakPathData` (agrees with the accepted
`chamberinv_ii`). -/
theorem X1_eq_of_mem_chamber' (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ chamber P) :
    X1 hn Q hQ = X1 hn P hP :=
  X1_eq_of_geoWeakPathData hn hP hQ (chamber_geoWeakPathData hn hP hQ h)

end CV
