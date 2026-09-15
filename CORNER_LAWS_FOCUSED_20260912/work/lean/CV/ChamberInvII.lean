import CV.ChamberInv
import CV.Carriers
import CV.CarrierBridges
import CV.X1
import SM.GeoPathTransport


/-! Ported 2026-09-14 04:54Z from work/drafts/cvdom/U5a/CVChamberInvII_partial.lean (CV-DOM unit U5a, report work/drafts/cvdom/U5a/REPORT.md). library towards CV:prop:chamberinv (ii): chamber paths transport Ind, N, U, pieces, wind, rotation, carrierR, groupedWrithe and the positive-lift HOMFLY; X1_eq_of_mem_chamber_of_pieceHomfly reduces (ii) to PieceHomflyTransported. Not a row. Only this header added. -/
/-! # CV/ChamberInvII (partial) — the chamber-constancy lemmas for CV:prop:chamberinv (ii)
(CV-DOM unit U5a, part 3)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §0, §3, §5 row **U5a**). Draft; intended home `work/lean/CV/ChamberInvII.lean`
(the row module of CV:prop:chamberinv (ii), d1_setup.tex:932–961, once `CV.X1` (row 146, unit U7c) exists —
the `X1` sum itself is left to the executor, §"What is left" of REPORT.md). Nothing under work/lean was written.

## Content

The CV-chamber instance of SM/GeoPathTransport.lean. Two CV-generic polygons of one CV chamber are joined by a
path of CV-generic polygons (the accepted CV:prop:chamberinv (i), `CV.chamber_joinedIn`); CV-generic polygons
are weakly generic (`CV.Generic.weakGeneric`, CV/Setup.lean:1135), hence `CarrierGeometry` (U0's
`CarrierGeometry.ofCV`) and on the record domain; so along the path the crossing supports, the same-edge
parameter order, the crossing signs and the vertex turns are constant (SM/GeoPathTransport.lean §2), which
gives a tier-2 path datum `GeoWeakPathData` between the two polygons (`chamber_geoWeakPathData`). From it,
for two polygons `P`, `Q` of one chamber, with the canonical identification `hs` of their crossing supports
(`crossing_iff_of_mem_chamber`):

* the vertex turns agree (`turn_eq_of_mem_chamber`); the complete geometric records agree
  (`geometricRecordsAgree_of_mem_chamber`);
* `Ind(G_P)` is carried onto `Ind(G_Q)` by `transportSupport hs` (`mem_Ind_transport_iff`, `Ind_eq_map`), and so
  are `N` and `U` (`N_transport`, `U_transport`) and the pieces (`pieceEquiv`, `pieceLabels_eq`,
  `pieceWrithe_eq`, `piecesOn_transport_eq`);
* CV:def:wind's `wt` and `wind` agree on corresponding independent sets (`weight_eq_of_mem_chamber`,
  `wind_eq_of_mem_chamber`), as does uniformity;
* the carrier rotations (`geoCarrierRotation`, hence CV:def:rot's `R(L)` of the corner polygon) and the HOMFLY
  polynomials of the positive lifts of corresponding carriers agree
  (`geoCarrierRotation_eq_of_mem_chamber`, `geoCarrierRotationInt_eq_of_mem_chamber`,
  `homfly_geoPositiveLift_eq_of_mem_chamber`), as do the numbers of retained crossings.

These are the ingredients of chamberinv (ii) ("X₁ is constant on each chamber"): every summand of `X1 hn P hG`
(d1_setup.tex:908–930) is a function of `wind`, of the carriers' `R(L)`, of the piece labels and of the piece
polynomials `P_H`, all carried by the canonical identification. Chambers are `CV.chamber` (CV:def:generic (B)):
no SM-chamber fallback; local constancy at a CV-generic `P` follows from `CV.chamber_mem_nhds`.

`hn : 3 ≤ n` is carried as in the row ("Fix `n ≥ 3`", d1_setup.tex:933) — the geo lemmas of U2b/U4 need it. -/

namespace CV

open SM SM.GeoCarrier SM.Carrier SM.Link

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

/-! ## 1. Chambers are paths of CV-generic polygons -/

/-- Every point of a chamber is generic (`chamber P ⊆ 𝓤_n`). -/
theorem generic_of_mem_chamber (h : Q ∈ chamber P) : Generic Q :=
  connectedComponentIn_subset (genericLocus n) P h

/-- Two polygons of one chamber are joined by a path of generic polygons (CV:prop:chamberinv (i),
`chamber_joinedIn`). -/
theorem exists_generic_path (hP : Generic P) (h : Q ∈ chamber P) :
    ∃ γ : Path P Q, ∀ t, Generic (γ t) := by
  obtain ⟨γ, hγ⟩ := chamber_joinedIn hP h
  exact ⟨γ, fun t => generic_of_mem_chamber (hγ t)⟩

/-! ## 2. The tier-2 path core and path datum of a chamber -/

/-- **Two CV-generic polygons of one chamber carry a tier-2 path core** (SM/GeoPathTransport.lean):
along the generic path of chamberinv (i) every polygon is weakly generic (`Generic.weakGeneric`). Standard
axioms. -/
theorem chamber_geoWeakPathCore_exists (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (h : Q ∈ chamber P) :
    ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s,
      GeoWeakPathCore (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ) hs := by
  obtain ⟨γ, hγ⟩ := exists_generic_path hP h
  exact GeoWeakPathCore.of_path hn γ (fun t => (hγ t).weakGeneric) _ _

/-- The crossing supports of two polygons of one chamber coincide (the canonical identification `hs`). -/
theorem crossing_iff_of_mem_chamber (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (h : Q ∈ chamber P) : ∀ s, IsCrossing P s ↔ IsCrossing Q s := by
  obtain ⟨hs, -⟩ := chamber_geoWeakPathCore_exists hn hP hQ h
  exact hs

/-- The tier-2 path core of a chamber, along the canonical identification. -/
theorem chamber_geoWeakPathCore (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ chamber P) :
    GeoWeakPathCore (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ)
      (crossing_iff_of_mem_chamber hn hP hQ h) := by
  obtain ⟨hs, d⟩ := chamber_geoWeakPathCore_exists hn hP hQ h
  exact d.congr_hs

/-- The tier-2 path datum of a chamber (core + HOMFLY clause), along the canonical identification. -/
theorem chamber_geoWeakPathData (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ chamber P) :
    GeoWeakPathData hn (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ)
      (crossing_iff_of_mem_chamber hn hP hQ h) := by
  obtain ⟨γ, hγ⟩ := exists_generic_path hP h
  obtain ⟨hs, d⟩ := GeoWeakPathData.of_path hn γ (fun t => (hγ t).weakGeneric)
    (CarrierGeometry.ofCV hP) (CarrierGeometry.ofCV hQ)
  exact d.congr_hs

/-- The mark transport of a chamber (marks, interlacement, signs), on the row binders. -/
theorem geoMarkTransport_of_mem_chamber (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q)
    (h : Q ∈ chamber P) :
    GeoMarkTransport hP.crossingGeometry hQ.crossingGeometry (crossing_iff_of_mem_chamber hn hP hQ h) :=
  (chamber_geoWeakPathCore hn hP hQ h).transport

/-! ## 3. Constancy on a chamber: records, turns, independent sets -/

section Chamber

variable (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ chamber P)
include hn hP hQ h

/-- Vertex turn signs are constant on a chamber. -/
theorem turn_eq_of_mem_chamber (i : ZMod n) : turn Q i = turn P i :=
  (chamber_geoWeakPathCore hn hP hQ h).turn_eq i

/-- The same-edge crossing-parameter order is constant on a chamber. -/
theorem crossingParameterOrderAgrees_of_mem_chamber : CrossingParameterOrderAgrees P Q :=
  (chamber_geoWeakPathCore hn hP hQ h).order_agrees

/-- Crossing signs are constant on a chamber. -/
theorem crossingSign_eq_of_mem_chamber (i j : ZMod n) (hij : IsCrossing P {i, j}) :
    crossingSign Q i j = crossingSign P i j :=
  (chamber_geoWeakPathCore hn hP hQ h).transport.sign_eq i j hij

/-- **The complete geometric records agree on a chamber** (`GeometricRecordsAgree`: crossing supports,
Gauss list and word, interlacement, signs). -/
theorem geometricRecordsAgree_of_mem_chamber :
    GeometricRecordsAgree hP.crossingGeometry hQ.crossingGeometry :=
  (chamber_geoWeakPathCore hn hP hQ h).recordsAgree

/-- Interlacement is constant on a chamber. -/
theorem geometricInterlaces_iff_of_mem_chamber (x y : Crossing P) :
    GeometricInterlaces hP.crossingGeometry x y ↔
      GeometricInterlaces hQ.crossingGeometry
        (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) x)
        (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) y) :=
  (geoMarkTransport_of_mem_chamber hn hP hQ h).interlaces_iff x y

/-- `Ind(G_P)` is carried onto `Ind(G_Q)` (CV:def:interlace, `CV.Ind`). -/
theorem mem_Ind_transport_iff (S : Finset (Crossing P)) :
    transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry ↔
      S ∈ Ind hP.crossingGeometry := by
  rw [mem_Ind_iff_geoIndependent, mem_Ind_iff_geoIndependent]
  exact (geoMarkTransport_of_mem_chamber hn hP hQ h).geoIndependent_iff S

/-- `Ind(G_Q)` is the image of `Ind(G_P)` under the support bijection (the reindexing of the `X1` sum). -/
theorem Ind_eq_map :
    Ind hQ.crossingGeometry =
      (Ind hP.crossingGeometry).map
        (GeoMarkTransport.supportEquiv (crossing_iff_of_mem_chamber hn hP hQ h)).toEmbedding := by
  ext S'
  rw [Finset.mem_map_equiv]
  obtain ⟨S, rfl⟩ := GeoMarkTransport.support_surjective (hs := crossing_iff_of_mem_chamber hn hP hQ h) S'
  rw [← GeoMarkTransport.supportEquiv_apply, Equiv.symm_apply_apply, GeoMarkTransport.supportEquiv_apply,
    mem_Ind_transport_iff hn hP hQ h S]

/-- The neighbourhood `N(S)` is carried. -/
theorem mem_N_transport_iff (S : Finset (Crossing P)) (y : Crossing P) :
    crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) y ∈
        N hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) ↔
      y ∈ N hP.crossingGeometry S := by
  rw [mem_N_iff, mem_N_iff]
  constructor
  · rintro ⟨x', hx', hI⟩
    obtain ⟨x, rfl⟩ := (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).surjective x'
    rw [GeoMarkTransport.mem_support] at hx'
    exact ⟨x, hx', (geometricInterlaces_iff_of_mem_chamber hn hP hQ h y x).mpr hI⟩
  · rintro ⟨x, hx, hI⟩
    exact ⟨crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) x,
      (GeoMarkTransport.mem_support S x).mpr hx,
      (geometricInterlaces_iff_of_mem_chamber hn hP hQ h y x).mp hI⟩

theorem N_transport (S : Finset (Crossing P)) :
    N hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) =
      transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) (N hP.crossingGeometry S) := by
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).surjective y'
  rw [mem_N_transport_iff hn hP hQ h S y, GeoMarkTransport.mem_support]

/-- The unselected complement `U(S)` is carried. -/
theorem mem_U_transport_iff (S : Finset (Crossing P)) (y : Crossing P) :
    crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) y ∈
        U hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) ↔
      y ∈ U hP.crossingGeometry S := by
  rw [mem_U, mem_U, GeoMarkTransport.mem_support, mem_N_transport_iff hn hP hQ h S y]

theorem U_transport (S : Finset (Crossing P)) :
    U hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) =
      transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) (U hP.crossingGeometry S) := by
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).surjective y'
  rw [mem_U_transport_iff hn hP hQ h S y, GeoMarkTransport.mem_support]

/-! ## 4. def:wind, rotations and positive lifts on a chamber -/

variable (S : Finset (Crossing P))

/-- CV:def:wind's weight of a carrier is constant on a chamber (`weight = geoCarrierSelector`). -/
theorem weight_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry) (q : GeoComponent hP.crossingGeometry S) :
    weight hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      weight hP.crossingGeometry S q :=
  (chamber_geoWeakPathCore hn hP hQ h).geoCarrierSelector_eq hn
    ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- **CV:def:wind's `wind(S)` is constant on a chamber** (the `wind` ingredient of chamberinv (ii)). -/
theorem wind_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry) :
    wind hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) =
      wind hP.crossingGeometry S :=
  (chamber_geoWeakPathCore hn hP hQ h).geoWind_eq hn ((mem_Ind_iff_geoIndependent _ S).mp hS)

/-- Uniformity of a carrier is constant on a chamber. -/
theorem carrierUniform_iff_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    CarrierUniform hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) ↔
      CarrierUniform hP.crossingGeometry S q :=
  (chamber_geoWeakPathCore hn hP hQ h).geoCarrierUniform_iff hn ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- The corner turns of a carrier are constant on a chamber (at the cast index). -/
theorem turn_geoCornerPolygon_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S)
    (j : ZMod (geoCornerCount hQ.crossingGeometry
      (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
      ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q))) :
    turn (geoCornerPolygon hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q)) j =
      turn (geoCornerPolygon hP.crossingGeometry S q)
        (Equiv.cast (congrArg ZMod
          ((geoMarkTransport_of_mem_chamber hn hP hQ h).geoCornerCount_eq S q)) j) :=
  (chamber_geoWeakPathCore hn hP hQ h).turn_geoCornerPolygon_eq hn ((mem_Ind_iff_geoIndependent _ S).mp hS) q j

/-- **The rotation of a carrier's corner polygon is constant on a chamber** (lem:rot (ii); CV:def:rot's
`R(L)` is a function of it). -/
theorem geoCarrierRotation_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    geoCarrierRotation hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      geoCarrierRotation hP.crossingGeometry S q :=
  (chamber_geoWeakPathCore hn hP hQ h).rotation_eq' ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- The same for the rotation number of the corner polygon itself. -/
theorem rotationNumber_geoCornerPolygon_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    rotationNumber (geoCornerPolygon hQ.crossingGeometry
        (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q)) =
      rotationNumber (geoCornerPolygon hP.crossingGeometry S q) :=
  geoCarrierRotation_eq_of_mem_chamber hn hP hQ h S hS q

theorem geoCarrierRotationInt_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    geoCarrierRotationInt hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      geoCarrierRotationInt hP.crossingGeometry S q :=
  (chamber_geoWeakPathCore hn hP hQ h).rotationInt_eq ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- **The HOMFLY polynomial of the positive lift of a carrier is constant on a chamber** (lit:homfly's
planar clause along the chamber path). -/
theorem homfly_geoPositiveLift_eq_of_mem_chamber (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : GeoIndependent (CarrierGeometry.ofCV hQ).cg
      (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S))
    (q : GeoComponent hP.crossingGeometry S) :
    homfly (geoPositiveLift hn (CarrierGeometry.ofCV hQ) hS'
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q)) =
      homfly (geoPositiveLift hn (CarrierGeometry.ofCV hP) ((mem_Ind_iff_geoIndependent _ S).mp hS) q) :=
  (chamber_geoWeakPathData hn hP hQ h).homfly_eq' ((mem_Ind_iff_geoIndependent _ S).mp hS) q

/-- The retained crossings of a carrier are carried. -/
theorem geoCarrierCrossings_eq_of_mem_chamber (q : GeoComponent hP.crossingGeometry S) :
    geoCarrierCrossings hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      (geoCarrierCrossings hP.crossingGeometry S q).map
        (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).toEmbedding :=
  (geoMarkTransport_of_mem_chamber hn hP hQ h).geoCarrierCrossings_eq S q

theorem card_geoCarrierCrossings_eq_of_mem_chamber (q : GeoComponent hP.crossingGeometry S) :
    (geoCarrierCrossings hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q)).card =
      (geoCarrierCrossings hP.crossingGeometry S q).card :=
  (geoMarkTransport_of_mem_chamber hn hP hQ h).card_geoCarrierCrossings_eq S q

/-! ## 5. Pieces on a chamber -/

/-- The canonical identification restricts to a bijection `U(S) → U(S')`. -/
theorem bijOn_U :
    Set.BijOn (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h))
      (↑(U hP.crossingGeometry S) : Set (Crossing P))
      (↑(U hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)) :
        Set (Crossing Q)) :=
  (crossingTransport _).bijOn fun y => by
    simp only [Finset.mem_coe]
    exact mem_U_transport_iff hn hP hQ h S y

/-- The residual graphs `G_P[U(S)]` and `G_Q[U(S')]` are isomorphic (`SimpleGraph.Iso.induce` of the
interlacement isomorphism). -/
noncomputable def residualIso :
    residualGraph hP.crossingGeometry S ≃g
      residualGraph hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) :=
  SimpleGraph.Iso.induce (geoMarkTransport_of_mem_chamber hn hP hQ h).interlacementIso
    (bijOn_U hn hP hQ h S)

/-- **The pieces of `S` correspond to the pieces of `S'`** (CV:def:pieces). -/
noncomputable def pieceEquiv :
    Piece hP.crossingGeometry S ≃
      Piece hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) :=
  (residualIso hn hP hQ h S).connectedComponentEquiv

theorem pieceEquiv_pieceOf (c : Crossing P) (hc : c ∈ U hP.crossingGeometry S) :
    pieceEquiv hn hP hQ h S (pieceOf hP.crossingGeometry S c hc) =
      pieceOf hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) c)
        ((mem_U_transport_iff hn hP hQ h S c).mpr hc) := by
  unfold pieceEquiv pieceOf
  rw [SimpleGraph.Iso.connectedComponentEquiv_apply, SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- The labels of a piece are carried. -/
theorem pieceLabels_eq (H : Piece hP.crossingGeometry S) :
    pieceLabels hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        (pieceEquiv hn hP hQ h S H) =
      (pieceLabels hP.crossingGeometry S H).map
        (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).toEmbedding := by
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_pieceLabels, mem_pieceLabels]
  constructor
  · rintro ⟨hc', hH⟩
    have hc : c ∈ U hP.crossingGeometry S := (mem_U_transport_iff hn hP hQ h S c).mp hc'
    refine ⟨hc, (pieceEquiv hn hP hQ h S).injective ?_⟩
    rw [pieceEquiv_pieceOf]
    exact hH
  · rintro ⟨hc, hH⟩
    refine ⟨(mem_U_transport_iff hn hP hQ h S c).mpr hc, ?_⟩
    rw [← pieceEquiv_pieceOf hn hP hQ h S c hc, hH]

/-- The writhe `w(H) = |H|` of a piece is carried. -/
theorem pieceWrithe_eq (H : Piece hP.crossingGeometry S) :
    pieceWrithe hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        (pieceEquiv hn hP hQ h S H) =
      pieceWrithe hP.crossingGeometry S H := by
  unfold pieceWrithe
  rw [pieceLabels_eq, Finset.card_map]

/-- The pieces assigned to a carrier are carried onto the pieces assigned to its copy. -/
theorem mem_piecesOn_transport_iff (q : GeoComponent hP.crossingGeometry S) (H : Piece hP.crossingGeometry S) :
    pieceEquiv hn hP hQ h S H ∈
        piecesOn hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
          ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) ↔
      H ∈ piecesOn hP.crossingGeometry S q := by
  rw [mem_piecesOn, mem_piecesOn, pieceLabels_eq]
  constructor
  · intro hall c hc v hv
    have := hall (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h) c)
      (Finset.mem_map_of_mem _ hc)
      (visitTransport (crossing_iff_of_mem_chamber hn hP hQ h) v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, (geoMarkTransport_of_mem_chamber hn hP hQ h).owner_transport] at this
    exact ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S).injective this
  · intro hall c' hc' w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hc'
    obtain ⟨v, rfl⟩ := (visitTransport (crossing_iff_of_mem_chamber hn hP hQ h)).surjective w
    rw [visitTransport_crossing] at hw
    have hv : v.1 = c := (crossingTransport (crossing_iff_of_mem_chamber hn hP hQ h)).injective hw
    rw [← markTransport_visit, GeoMarkTransport.owner_transport, hall c hc v hv]

theorem piecesOn_transport_eq (q : GeoComponent hP.crossingGeometry S) :
    piecesOn hQ.crossingGeometry (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S)
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      (piecesOn hP.crossingGeometry S q).map (pieceEquiv hn hP hQ h S).toEmbedding := by
  ext H'
  obtain ⟨H, rfl⟩ := (pieceEquiv hn hP hQ h S).surjective H'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_piecesOn_transport_iff]

end Chamber

/-! ## 6. Local form -/

/-- Every CV-generic polygon has a neighbourhood inside its chamber (chamberinv (i)): the chamber-constancy
lemmas above hold eventually near `P`. -/
theorem Generic.eventually_mem_chamber (hP : Generic P) : ∀ᶠ Q in nhds P, Q ∈ chamber P :=
  chamber_mem_nhds hP

/-! ## 7. `X₁` on a chamber, modulo the piece polynomials

`CV.X1` (row 146, CV/X1.lean, landed 2026-09-14 04:34Z) is
`∑_{S ∈ Ind} wind(S) ∏_L Ω₁(S,L)`, `Ω₁(S,L) = [a^{1−w_{S,L}−R(L)} z⁰] P_{S,L}`, `P_{S,L} = ∏_{H ∈ piecesOn L} P_H`,
`w_{S,L} = ∑_{H ∈ piecesOn L} w(H)`, `R(L) = |rot|` of the carrier's corner polygon. Every ingredient except `P_H`
is carried by the chamber transport above; `P_H = pieceHomfly` is the HOMFLY polynomial of the positive lift of
the carrier of `S ∪ pieceSupport H` carrying `H`, where `pieceSupport` is a `Classical.choose` (CV/PieceCurve.lean)
— its value at `Q` is not literally the transport of its value at `P`, so its constancy is a separate lemma
(`PieceHomflyTransported`, the one open point; see REPORT.md §6). Given it, `X₁` is constant on the chamber
(`X1_eq_of_mem_chamber_of_pieceHomfly`). -/

section X1Chamber

variable (hn : 3 ≤ n) (hP : Generic P) (hQ : Generic Q) (h : Q ∈ chamber P)
include hn hP hQ h

/-- `w_{S,L}` is carried (`piecesOn_transport_eq`, `pieceWrithe_eq`). -/
theorem groupedWrithe_eq_of_mem_chamber (S : Finset (Crossing P)) (q : GeoComponent hP.crossingGeometry S) :
    groupedWrithe hQ ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      groupedWrithe hP q := by
  unfold groupedWrithe
  rw [piecesOn_transport_eq hn hP hQ h S q, Finset.sum_map]
  exact Finset.sum_congr rfl fun H _ => pieceWrithe_eq hn hP hQ h S H

/-- `R(L) = |rot(L)|` is carried (`rot_eq_rotationNumber` and the chamber constancy of the rotation number of
the corner polygon). -/
theorem carrierR_eq_of_mem_chamber (S : Finset (Crossing P)) (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    carrierR hn hQ hS' ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      carrierR hn hP hS q := by
  unfold carrierR rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [rot_eq_rotationNumber, rot_eq_rotationNumber]
  exact rotationNumber_geoCornerPolygon_eq_of_mem_chamber hn hP hQ h S hS q

/-- **The open hypothesis**: the piece polynomials `P_H` are carried by the piece bijection of the chamber
transport. (Every other ingredient of `X₁` is proved to be carried below; this one waits for the
choice-independence of `pieceSupport`, REPORT.md §6.) -/
def PieceHomflyTransported : Prop :=
  ∀ (S : Finset (Crossing P)) (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry)
    (H : Piece hP.crossingGeometry S),
    pieceHomfly hn (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H) =
      pieceHomfly hn (hP.diagrammatic hn) hS H

/-- `P_{S,L}` is carried, given `PieceHomflyTransported`. -/
theorem groupedPoly_eq_of_mem_chamber (hPH : PieceHomflyTransported hn hP hQ h) (S : Finset (Crossing P))
    (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    groupedPoly hn hQ hS' ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) =
      groupedPoly hn hP hS q := by
  unfold groupedPoly
  rw [piecesOn_transport_eq hn hP hQ h S q, Finset.prod_map]
  exact Finset.prod_congr rfl fun H _ => hPH S hS hS' H

/-- The slot `1 − w_{S,L} − R(L)` is carried. -/
theorem slot_eq_of_mem_chamber (S : Finset (Crossing P)) (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    slot hn hQ hS' ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) = slot hn hP hS q := by
  unfold slot
  rw [groupedWrithe_eq_of_mem_chamber hn hP hQ h S q, carrierR_eq_of_mem_chamber hn hP hQ h S hS hS' q]

/-- The factor `Ω₁(S,L)` is carried, given `PieceHomflyTransported`. -/
theorem Omega1_eq_of_mem_chamber (hPH : PieceHomflyTransported hn hP hQ h) (S : Finset (Crossing P))
    (hS : S ∈ Ind hP.crossingGeometry)
    (hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry)
    (q : GeoComponent hP.crossingGeometry S) :
    Omega1 hn hQ hS' ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S q) = Omega1 hn hP hS q := by
  unfold Omega1
  rw [slot_eq_of_mem_chamber hn hP hQ h S hS hS' q, groupedPoly_eq_of_mem_chamber hn hP hQ h hPH S hS hS' q]

/-- The summand of `X₁` at `S`, as a total function of the support (the device of the accepted
`cornerStateSum_transport`). -/
noncomputable def X1Summand (hG : Generic P) (S : Finset (Crossing P)) : ℤ :=
  open scoped Classical in
  if hS : S ∈ Ind hG.crossingGeometry then
    wind hG.crossingGeometry S * ∏ q : GeoComponent hG.crossingGeometry S, Omega1 hn hG hS q
  else 0

omit hP hQ h in
/-- `X₁` is the sum of the total summands over `Ind`. -/
theorem X1_eq_sum_X1Summand (hG : Generic P) :
    X1 hn P hG = ∑ S ∈ Ind hG.crossingGeometry, X1Summand hn hG S := by
  unfold X1
  rw [← Finset.sum_attach (Ind hG.crossingGeometry) (X1Summand hn hG)]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold X1Summand
  rw [dite_eq_left S.2]

/-- The summand is carried, given `PieceHomflyTransported`. -/
theorem X1Summand_eq_of_mem_chamber (hPH : PieceHomflyTransported hn hP hQ h) (S : Finset (Crossing P)) :
    X1Summand hn hQ (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S) = X1Summand hn hP S := by
  unfold X1Summand
  by_cases hS : S ∈ Ind hP.crossingGeometry
  · have hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∈ Ind hQ.crossingGeometry :=
      (mem_Ind_transport_iff hn hP hQ h S).mpr hS
    rw [dite_eq_left hS, dite_eq_left hS', wind_eq_of_mem_chamber hn hP hQ h S hS]
    congr 1
    exact (Fintype.prod_equiv ((geoMarkTransport_of_mem_chamber hn hP hQ h).component S) _ _
      fun q => (Omega1_eq_of_mem_chamber hn hP hQ h hPH S hS hS' q).symm).symm
  · have hS' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∉ Ind hQ.crossingGeometry :=
      fun h' => hS ((mem_Ind_transport_iff hn hP hQ h S).mp h')
    rw [dite_eq_right hS, dite_eq_right hS']

/-- **CV:prop:chamberinv (ii) modulo the piece polynomials**: `X₁` takes the same value at two CV-generic
polygons of one CV chamber, provided the piece polynomials are carried (`PieceHomflyTransported`). The sum over
`Ind(G_Q)` is reindexed along the support bijection (`Ind_eq_map`), `wind` by `wind_eq_of_mem_chamber`, the
product over carriers along `τ.component S`, and each `Ω₁` by `Omega1_eq_of_mem_chamber`. -/
theorem X1_eq_of_mem_chamber_of_pieceHomfly (hPH : PieceHomflyTransported hn hP hQ h) :
    X1 hn Q hQ = X1 hn P hP := by
  rw [X1_eq_sum_X1Summand hn hQ, X1_eq_sum_X1Summand hn hP, Ind_eq_map hn hP hQ h, Finset.sum_map]
  exact Finset.sum_congr rfl fun S _ => X1Summand_eq_of_mem_chamber hn hP hQ h hPH S

end X1Chamber

end CV
