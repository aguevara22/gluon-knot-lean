import CV.ChamberInvII
import CV.PieceIntrinsic


/-! Ported 2026-09-14 06:45Z from work/drafts/cvdom/U5c/PieceHomflyTransport.lean (CV-DOM unit U5c, report work/drafts/cvdom/U5c/REPORT.md): library: choice-independence of the piece polynomial at one polygon (homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq via CV.exists_recordIso_of_geoCarrierCrossings_eq + gausscode_polynomial) and its chamber transport PieceHomflyTransported (pieceHomflyTransported). Only this header added. -/
/-! # CV/PieceHomflyTransport — the piece polynomials are carried along a chamber
(CV-DOM unit U5c; closes the one open lemma of CV/ChamberInvII.lean)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor (CV-DOM decision,
work/drafts/cvdom/DECISION_FINAL.md §5 row U5a, §6 item 6; U5a report §6 "recommended route").
Intended home `work/lean/CV/PieceHomflyTransport.lean`. Nothing under work/lean was written.

## What is proved

`CV.pieceHomflyTransported hn hP hQ h : PieceHomflyTransported hn hP hQ h` for every pair of CV-generic
polygons `P`, `Q` of one CV chamber: the piece polynomial `P_H = pieceHomfly` (CV:def:piecediagram,
`homfly` of the positive lift of the carrier `q_H` of `S ∪ K_H` carrying the piece `H`) is carried by the
piece bijection `pieceEquiv` of the chamber transport. With it, `CV.X1_eq_of_mem_chamber_of_pieceHomfly`
(CV/ChamberInvII.lean) gives CV:prop:chamberinv (ii).

## Route (U5a report §6, item 2 — the record route)

`pieceSupport` is a `Classical.choose`, so the support chosen at `Q` need not be the transport of the
support chosen at `P`. Two steps:

1. **Choice independence at one polygon** (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`): on a
   fixed polygon (tier 1, `hG : CarrierGeometry`), two carriers of two independent supports with the same
   retained crossings have positive lifts with isomorphic records — the accepted row CV:lem:pieceintrinsic
   (CV/PieceIntrinsic.lean, `exists_recordIso_of_geoCarrierCrossings_eq`: CV:def:record's clauses (a)–(d)
   for "the identity map on the visits of `H`", d6:67) — hence the same HOMFLY polynomial by the accepted
   CV:ax:gausscode replacement `gausscode_polynomial`.
2. **Transport along the chamber** (`pieceHomflyTransported`): at `Q`, the carrier of `S' ∪ K'` (the support
   chosen at `Q`) and the transported carrier of `S' ∪ tK` (the support chosen at `P`, carried by
   `geoMarkTransport_of_mem_chamber`) have the same retained crossings — the labels of the piece
   (`pieceCarrier_geoCarrierCrossings`, `pieceLabels_eq`, `geoCarrierCrossings_eq_of_mem_chamber`) — so
   step 1 applies; and the transported carrier's lift has the HOMFLY polynomial of the lift at `P` by U5a's
   `homfly_geoPositiveLift_eq_of_mem_chamber` (lit:homfly's planar clause along the chamber path).

A self-contained proof of step 1 (not importing CV/PieceIntrinsic; block coordinates of the carrier's
marks, orbit of `TracedSuccessor`, record isomorphism) is kept as
work/drafts/cvdom/U5c/PieceHomflyTransport_selfcontained.lean (same two theorem names; cross-check).

Everything is on the printed binders (`hP hQ : CV.Generic`, `h : Q ∈ CV.chamber P`). Axioms: standard plus
`SM.lit_homfly` (through `homfly`). -/

namespace CV

open SM SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

/-! ## 1. Choice independence of the positive lift's HOMFLY polynomial at one polygon -/

/-- **Two carriers with the same retained crossings have positive lifts with the same HOMFLY polynomial**
(on one polygon, tier 1): their records are isomorphic (CV:lem:pieceintrinsic,
`exists_recordIso_of_geoCarrierCrossings_eq`) and the accepted CV:ax:gausscode replacement
`gausscode_polynomial` gives the equality of polynomials. -/
theorem homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq {n : ℕ} [NeZero n] {Q : LabelledTuple n}
    (hn : 3 ≤ n) (hG : CarrierGeometry Q) {T₁ T₂ : Finset (Crossing Q)}
    (hT₁ : GeoIndependent hG.cg T₁) (hT₂ : GeoIndependent hG.cg T₂)
    (q₁ : GeoComponent hG.cg T₁) (q₂ : GeoComponent hG.cg T₂)
    (hH : geoCarrierCrossings hG.cg T₁ q₁ = geoCarrierCrossings hG.cg T₂ q₂) :
    homfly (geoPositiveLift hn hG hT₁ q₁) = homfly (geoPositiveLift hn hG hT₂ q₂) := by
  obtain ⟨ι, -⟩ := exists_recordIso_of_geoCarrierCrossings_eq hn hG hT₁ hT₂ q₁ q₂ hH
  exact gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hT₁ q₁)
    (geoPositiveLift_componentCount hn hG hT₂ q₂) ι

/-! ## 2. The chamber transport of the piece polynomials -/

/-- **The piece polynomials are carried along a chamber** (the open hypothesis of CV/ChamberInvII.lean):
at `Q` the carrier of `S' ∪ K'` (the support chosen at `Q`) and the transport of the carrier of `S ∪ K_H`
(the support chosen at `P`) both carry exactly the labels of the piece, so their positive lifts have the same
HOMFLY polynomial (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`), and the transported lift has the
polynomial of the lift at `P` (`homfly_geoPositiveLift_eq_of_mem_chamber`, lit:homfly's planar clause along
the chamber path). -/
theorem pieceHomflyTransported {n : ℕ} [NeZero n] {P Q : LabelledTuple n} (hn : 3 ≤ n) (hP : Generic P)
    (hQ : Generic Q) (h : Q ∈ chamber P) : PieceHomflyTransported hn hP hQ h := by
  intro S hS hS' H
  have hSK : S ∪ pieceSupport (hP.diagrammatic hn) hS H ∈ Ind hP.crossingGeometry :=
    pieceSupport_mem_Ind (hP.diagrammatic hn) hS H
  have hSK' : transportSupport (crossing_iff_of_mem_chamber hn hP hQ h)
      (S ∪ pieceSupport (hP.diagrammatic hn) hS H) ∈ Ind hQ.crossingGeometry :=
    (mem_Ind_transport_iff hn hP hQ h _).mpr hSK
  have hK2 : GeoIndependent (CarrierGeometry.ofCV hQ).cg (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h)
      (S ∪ pieceSupport (hP.diagrammatic hn) hS H)) :=
    geoIndependent_of_mem_Ind _ hSK'
  have hcross : geoCarrierCrossings hQ.crossingGeometry
      (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) S ∪
        pieceSupport (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H))
      (pieceCarrier (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H)) =
      geoCarrierCrossings hQ.crossingGeometry
        (transportSupport (crossing_iff_of_mem_chamber hn hP hQ h) (S ∪ pieceSupport (hP.diagrammatic hn) hS H))
        ((geoMarkTransport_of_mem_chamber hn hP hQ h).component _ (pieceCarrier (hP.diagrammatic hn) hS H)) := by
    rw [pieceCarrier_geoCarrierCrossings, pieceLabels_eq hn hP hQ h S H,
      geoCarrierCrossings_eq_of_mem_chamber hn hP hQ h, pieceCarrier_geoCarrierCrossings]
  unfold pieceHomfly pieceDiagram
  rw [homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic (hQ.diagrammatic hn))
    (pieceSupport_geoIndependent (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H)) hK2
    (pieceCarrier (hQ.diagrammatic hn) hS' (pieceEquiv hn hP hQ h S H)) _ hcross]
  exact homfly_geoPositiveLift_eq_of_mem_chamber hn hP hQ h _ hSK hK2 (pieceCarrier (hP.diagrammatic hn) hS H)

end CV
