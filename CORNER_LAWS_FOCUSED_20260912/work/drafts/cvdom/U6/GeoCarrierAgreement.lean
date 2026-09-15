import SM.CS3
import SM.GeoCarriersLemma
import SM.GeoPositiveLift
import SM.CBBlocks
import CV.X1

/-! # SM/GeoCarrierAgreement.lean — CV-DOM unit U6: the agreement on an SM-generic polygon

Draft (work/drafts/cvdom/U6/), intended home `work/lean/SM/GeoCarrierAgreement.lean`.
Spec: work/drafts/cvdom/DECISION_FINAL.md §5 row U6, §7 risk 2 and 6, ruling R7; BRIDGE.md B4 parts 1-4
((13)-(17)).  Library module: no row is stated here; the row module is `Bridge/B4.lean` (draft
work/drafts/cvdom/U6/BridgeB4.lean).

## What is proved

On an SM-generic polygon `P` (`hn : 3 ≤ n`, `hP : SM.Generic P`), read on the geometric record domain
`hc := generic_crossingGeometry hn hP` with the accepted carrier equivalence
`e := geoComponentEquivGeneric hn hP S : GeoComponent hc S ≃ Component hn hP S` (def:flat-carriers), for
every `S ∈ Ind(G_P)`:

* §1 (SM side, `SM.GeoCarrier`): the def:uniform data of U3's geo lane are the accepted def:uniform data of
  the carrier `e q` — `geoCarrierRotation_eq_generic`, `geoCarrierRotationInt_eq_generic`,
  `geoCarrierLeftTurns_eq_generic`, `geoCarrierSelector_eq_carrierWeight`, `geoUniformSupport_iff_generic`
  (re-export), and `geoWind_eq_generic` (re-export of U3).  The corner polygons agree only up to the recast
  along the equal corner counts (`SM.geoCornerPolygon_eq_generic`, accepted CS3 §B), so these lemmas go
  through `rotationNumber_recastTuple` / `leftTurns_recastTuple` (the one non-`rfl` agreement point,
  DECISION_FINAL §7 risk 2).
* §2 (CV side, `CV`): CV:def:X1's per-carrier data at the CV-generic proof `hG := generic_of_sm hn hP`
  (any `hG : CV.Generic P`, all proofs of a `Prop` being definitionally equal) are def:C's data of `e q`:
  `wind_eq_generic` (CV:def:wind = lem:C-X1's `wind`), `groupedWrithe_eq_generic` (`w_{S,L} = m_L`, BRIDGE.md
  (13) second equality), `carrierR_eq_generic` (`R(L) = |r_L|`, (14)), `slot_eq_generic` (`1 − w − R = d_L`,
  (15)); and, FROM the fixed cb:products bundle `SM.CbProductsData hn hP hS` (row 102) as an explicit
  hypothesis, `groupedPoly_eq_cornerHomfly_of_cb` (`P_{S,L} = ∏_H P_H = P_L = H⁺_L`, (13) first equality)
  and `Omega1_eq_cornerCoefficient_of_cb` (`Ω₁(S,L) = c(L)`, (16)).
* §3: the state sums: `CV.X1_eq_cornerStateSum_of_cb` — `X₁(P) = C(P)` (17) from the accepted lem:C-X1
  selector form (`SM.C_X1.selector_form`), `CV.Ind_eq_generic`, the attached-sum transport
  `sum_attach_congr`, `Fintype.prod_equiv e`.

## Readings (recorded for the reviewer; BRIDGE.md B4 parts 1-4)

1. BRIDGE.md part 2 ("common carriers"): the carrier `L` of CV is `q : GeoComponent hc S`, the carrier of SM
   is `e q : Component hn hP S`; `e` is the accepted identity-on-marks equivalence
   (`geoComponentEquivGeneric_owner` is `rfl`).  Ownership of the two visits of a selected crossing is SM
   conv:selected-visits on both sides (the same `selectedMarkPerm`).
2. BRIDGE.md part 3 / (13): `P_{S,L} = ∏_{H on L} P_H` equals `H⁺_L = homfly (positiveLift L)` through
   cb:products' product formula `P_A = ∏_{H owned by A} P_H` (`CbProductsData.product`) with `P_A = SM.P D_A =
   homfly D_A` (`P_eq_homfly`, lp:core) and `P_H = blockPoly H = SM.P (pieceDiagram H)`
   (`CbProductsData.polynomial_independent`, applied to CV's `pieceDiagram H`, which IS an actual positive
   carrier diagram of `H`: `isBlockCarrierDiagram_pieceDiagram`, through the accepted
   `geoPositiveLift_eq_generic` and `pieceCarrier_geoCarrierCrossings`).  The CV grouping "pieces assigned
   to `L`" is literally cb:blocks' "blocks owned by `A`" (`SM.CB.blocksOwnedBy hn hP S (e q) = piecesOn hc S q`,
   by `Equiv.symm_apply_apply`).
3. BRIDGE.md (13) second equality: `w_{S,L} = Σ_{H on L} |H| = m_L` is U7c's
   `groupedWrithe_eq_card_geoCarrierCrossings` + the accepted `geoCarrierCrossings_eq_generic`.
4. BRIDGE.md (14): `R(L) = |rot(L)|` with CV's integer `rot` (CV:def:rot, `rot_eq_rotationNumber` =
   lem:turnlift (ii)) and SM's `r_L = rotationNumber (ccpCornerPolygon …)` (def:uniform), an integer by lem:rot
   (`carrierRotationInt_cast`): `carrierR_eq_generic` is `R(L) = |carrierRotationInt (e q)|` in `ℤ`.
5. BRIDGE.md (16)-(17): "This argument includes absent monomials, whose coefficients are zero. It imposes no
   sign gate or nonzero gate": both sides are `coeffAt slot 0 poly` (`SM.coeffAt`, zero off the support), and
   the sum over `Ind(G_P)` uses lem:C-X1's `selector_form` (non-uniform supports contribute `wind = 0` on both
   sides — no uniformity filter is compared).
6. `hn : 3 ≤ n` is a binder throughout (def:C and CV:def:X1 both carry it; reading (iii) of DECISION_FINAL §2).

Checked with `cd work/lean && lake env lean ../drafts/cvdom/U6/GeoCarrierAgreement.lean` (all imports are
modules of work/lean). -/

namespace SM

open Link Carrier GeoCarrier

attribute [local instance] Classical.propDecidable

/-! ## 0. Two hypothesis-free helpers -/

/-- The number of left turns is unchanged by a recast along an equality of sizes (companion of
`rotationNumber_recastTuple`, `forall_turn_recastTuple`, SM/CChamber.lean §0). -/
theorem leftTurns_recastTuple {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k) (f : LabelledTuple k) :
    leftTurns (recastTuple hk f) = leftTurns f := by
  subst hk; rfl

/-- Transport of an attached sum along an equality of index finsets: the shape in which `X₁`'s sum over
`(Ind hc).attach` is compared with `C`'s sum over `(independentSupports hn hP).attach`. -/
theorem sum_attach_congr {α β : Type*} [AddCommMonoid β] {s t : Finset α} (hst : s = t)
    (f : {x // x ∈ s} → β) (g : {x // x ∈ t} → β)
    (h : ∀ (x : α) (hs : x ∈ s) (ht : x ∈ t), f ⟨x, hs⟩ = g ⟨x, ht⟩) :
    ∑ x ∈ s.attach, f x = ∑ x ∈ t.attach, g x := by
  subst hst
  exact Finset.sum_congr rfl fun x _ => h x.1 x.2 x.2

namespace GeoCarrier

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P) (S : Finset (Crossing P))

/-! ## 1. def:uniform's data agree (SM side) -/

/-- `r_L`: the geo rotation of the carrier `q` is the accepted `carrierRotation` of `e q`
(`SM.carrierRotation_eq_geo`, CS3 §B, through the recast corner polygon and `rotationNumber_recastTuple`). -/
theorem geoCarrierRotation_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierRotation (generic_crossingGeometry hn hP) S q =
      carrierRotation hn hP S (geoComponentEquivGeneric hn hP S q) :=
  (carrierRotation_eq_geo hn hP S q).symm

/-- The integer rotations agree. -/
theorem geoCarrierRotationInt_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierRotationInt (generic_crossingGeometry hn hP) S q =
      carrierRotationInt hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoCarrierRotationInt carrierRotationInt
  rw [geoCarrierRotation_eq_generic hn hP S q]

/-- `ℓ_L`: the numbers of left turns agree (`leftTurns_recastTuple`). -/
theorem geoCarrierLeftTurns_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierLeftTurns (generic_crossingGeometry hn hP) S q =
      carrierLeftTurns hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold geoCarrierLeftTurns carrierLeftTurns
  rw [geoCornerPolygon_eq_generic hn hP S q, leftTurns_recastTuple]

/-- The accepted selector of cor:flat-carriers (iii) is lem:C-X1's weight `wt(L)` of `e q`
(`SM.carrierWeight_eq_geoCarrierSelector`, CS3 §B). -/
theorem geoCarrierSelector_eq_carrierWeight (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    geoCarrierSelector (generic_crossingGeometry hn hP) S q =
      carrierWeight hn hP S (geoComponentEquivGeneric hn hP S q) :=
  (carrierWeight_eq_geoCarrierSelector hn hP S q).symm

/-- The retained-crossing counts agree (`m_L`; U4's `geoCarrierCrossings_eq_generic`). -/
theorem card_geoCarrierCrossings_eq_generic (q : GeoComponent (generic_crossingGeometry hn hP) S) :
    (geoCarrierCrossings (generic_crossingGeometry hn hP) S q).card =
      carrierCrossingCount hn hP S (geoComponentEquivGeneric hn hP S q) := by
  rw [geoCarrierCrossings_eq_generic hn hP S q, carrierCrossingCount_eq_card]

end GeoCarrier

end SM

namespace CV

open SM SM.Carrier SM.GeoCarrier SM.Link

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] (hn : 3 ≤ n) {P : LabelledTuple n} (hP : SM.Generic P)

/-! ## 2. CV:def:X1's per-carrier data at an SM-generic polygon are def:C's data

Notation: `hG : CV.Generic P` (in the bridge, `CV.generic_of_sm hn hP`; every `CV.*` object below depends on
`hG` only through proofs of `Prop`s, so any two such proofs give definitionally equal objects),
`hS : S ∈ Ind hG.crossingGeometry` (the CV row binder), `hS' : IsDecomposition hn hP S` (def:C's binder; the
two are the same set by `CV.Ind_eq_generic`), `e := geoComponentEquivGeneric hn hP S`. -/

/-- `S ∈ Ind(G_P)` on the CV side is def:decomposition's `IsDecomposition` (`CV.Ind_eq_generic`). -/
theorem isDecomposition_of_mem_Ind (hc : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : S ∈ Ind hc) : IsDecomposition hn hP S := by
  rw [Ind_eq_generic hn hP hc] at hS
  exact hS

theorem mem_Ind_of_isDecomposition (hc : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : IsDecomposition hn hP S) : S ∈ Ind hc := by
  rw [Ind_eq_generic hn hP hc]
  exact hS

section PerCarrier

variable (hG : Generic P) {S : Finset (Crossing P)}

/-- **CV:def:wind = lem:C-X1's `wind`** on an SM-generic polygon (BRIDGE.md part 4, "their products over the
common carriers agree"): U3's `geoWind_eq_generic` (`CV.wind` and `geoWind` are both
`∏_q geoCarrierSelector`). -/
theorem wind_eq_generic (hS' : IsDecomposition hn hP S) : wind hG.crossingGeometry S = SM.wind hn hP S :=
  geoWind_eq_generic hn hP hS'

/-- **`w_{S,L} = m_L`** (BRIDGE.md (13), second equality): the grouped writhe of the carrier `q` is def:smoothing's
crossing number of `e q` (U7c `groupedWrithe_eq_card_geoCarrierCrossings` + `geoCarrierCrossings_eq_generic`). -/
theorem groupedWrithe_eq_generic (hS : S ∈ Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    groupedWrithe hG q = (carrierCrossingCount hn hP S (geoComponentEquivGeneric hn hP S q) : ℤ) := by
  rw [groupedWrithe_eq_card_geoCarrierCrossings hG hS q]
  exact congrArg _ (card_geoCarrierCrossings_eq_generic hn hP S q)

/-- **`R(L) = |r_L|`** (BRIDGE.md (14)): CV:def:rot's `R(L)` of the corner polygon of `q` is the absolute value of
def:C's integer rotation `carrierRotationInt` of `e q` (CV `rot_eq_rotationNumber` = lem:turnlift (ii),
`carrierRotationInt_cast` = lem:rot, `carrierRotation_eq_geo` = the recast). -/
theorem carrierR_eq_generic (hS : S ∈ Ind hG.crossingGeometry) (hS' : IsDecomposition hn hP S)
    (q : GeoComponent hG.crossingGeometry S) :
    (carrierR hn hG hS q : ℤ) = |carrierRotationInt hn hP S (geoComponentEquivGeneric hn hP S q)| := by
  rw [carrierR_cast]
  congr 1
  have h1 := rot_eq_rotationNumber (carrierPolygon_cvRegular hn hG hS q)
  have h2 := carrierRotationInt_cast hn hP hS' (geoComponentEquivGeneric hn hP S q)
  have h3 := carrierRotation_eq_geo hn hP S q
  have h : ((rot (geoCornerPolygon hG.crossingGeometry S q) (carrierPolygon_cvRegular hn hG hS q) : ℤ) : ℝ) =
      ((carrierRotationInt hn hP S (geoComponentEquivGeneric hn hP S q) : ℤ) : ℝ) :=
    h1.trans (h3.symm.trans h2.symm)
  exact_mod_cast h

/-- **The slot `1 − w_{S,L} − R(L)` is def:C's exponent `d_L`** (BRIDGE.md (15)). -/
theorem slot_eq_generic (hS : S ∈ Ind hG.crossingGeometry) (hS' : IsDecomposition hn hP S)
    (q : GeoComponent hG.crossingGeometry S) :
    slot hn hG hS q = cornerSlot hn hP S (geoComponentEquivGeneric hn hP S q) := by
  unfold slot cornerSlot
  rw [groupedWrithe_eq_generic hn hP hG hS q, carrierR_eq_generic hn hP hG hS hS' q]

/-- **CV's piece diagram is an actual positive carrier diagram of its block** (cb:products' `D_H`, reading R-4 of
SM/CBBlocks.lean): `pieceDiagram H` is the accepted `positiveLift` of the carrier `e (q_H)` of the refinement
`S ∪ K_H ⊇ S` (`geoPositiveLift_eq_generic`), whose self-crossings are exactly the labels of `H`
(`pieceCarrier_geoCarrierCrossings`, `geoCarrierCrossings_eq_generic`). -/
theorem isBlockCarrierDiagram_pieceDiagram (hS : S ∈ Ind hG.crossingGeometry)
    (hS' : IsDecomposition hn hP S) (H : Piece hG.crossingGeometry S) :
    SM.CB.IsBlockCarrierDiagram hn hP hS' H (pieceDiagram hn (hG.diagrammatic hn) hS H) := by
  have hT : IsDecomposition hn hP (S ∪ pieceSupport (hG.diagrammatic hn) hS H) :=
    isDecomposition_of_mem_Ind hn hP _ (pieceSupport_mem_Ind (hG.diagrammatic hn) hS H)
  refine ⟨S ∪ pieceSupport (hG.diagrammatic hn) hS H, hT,
    geoComponentEquivGeneric hn hP _ (pieceCarrier (hG.diagrammatic hn) hS H),
    Finset.subset_union_left, ?_, ?_⟩
  · rw [← geoCarrierCrossings_eq_generic hn hP _ (pieceCarrier (hG.diagrammatic hn) hS H)]
    exact pieceCarrier_geoCarrierCrossings (hG.diagrammatic hn) hS H
  · exact geoPositiveLift_eq_generic hn hP _ (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
      (pieceSupport_geoIndependent (hG.diagrammatic hn) hS H) hT
      (pieceCarrier (hG.diagrammatic hn) hS H)

/-- The pieces assigned to the carrier `q` (CV:def:X1, lem:carriers (iv)) are cb:blocks' blocks owned by the
carrier `e q` (`SM.CB.blocksOwnedBy`), literally. -/
theorem blocksOwnedBy_eq_piecesOn (q : GeoComponent hG.crossingGeometry S) :
    SM.CB.blocksOwnedBy hn hP S (geoComponentEquivGeneric hn hP S q) = piecesOn hG.crossingGeometry S q := by
  unfold SM.CB.blocksOwnedBy
  rw [Equiv.symm_apply_apply]

/-- **`P_H = blockPoly H`** from cb:products: CV's piece polynomial `P_H = homfly (pieceDiagram H)` is the
polynomial of the restricted named record of `H` (`CbProductsData.polynomial_independent` at the actual positive
carrier diagram `pieceDiagram H`, and `P_eq_homfly`). -/
theorem pieceHomfly_eq_blockPoly_of_cb (hS : S ∈ Ind hG.crossingGeometry) (hS' : IsDecomposition hn hP S)
    (hcb : CbProductsData hn hP hS') (H : Piece hG.crossingGeometry S) :
    pieceHomfly hn (hG.diagrammatic hn) hS H = SM.CB.blockPoly hn hP hS' H := by
  have h := (hcb.polynomial_independent H _ (isBlockCarrierDiagram_pieceDiagram hn hP hG hS hS' H)).2
  rw [← h, P_eq_homfly]
  rfl

/-- **`P_{S,L} = H⁺_L`** (BRIDGE.md (13), first equality) from cb:products: `∏_{H on L} P_H = ∏_{H owned by A} P_H =
P_A = homfly (positiveLift A)` for `A = e q` (`CbProductsData.product`, `P_eq_homfly`, `pieceHomfly_eq_blockPoly_of_cb`). -/
theorem groupedPoly_eq_cornerHomfly_of_cb (hS : S ∈ Ind hG.crossingGeometry) (hS' : IsDecomposition hn hP S)
    (hcb : CbProductsData hn hP hS') (q : GeoComponent hG.crossingGeometry S) :
    groupedPoly hn hG hS q = cornerHomfly hn hP S (geoComponentEquivGeneric hn hP S q) hS' := by
  have hprod := hcb.product (geoComponentEquivGeneric hn hP S q)
  unfold SM.CB.carrierPoly at hprod
  rw [P_eq_homfly, blocksOwnedBy_eq_piecesOn hn hP hG q] at hprod
  unfold cornerHomfly groupedPoly
  rw [hprod]
  exact Finset.prod_congr rfl fun H _ => pieceHomfly_eq_blockPoly_of_cb hn hP hG hS hS' hcb H

/-- **`Ω₁(S,L) = c(L)`** (BRIDGE.md (16)) from cb:products: equal polynomials read at equal slots. -/
theorem Omega1_eq_cornerCoefficient_of_cb (hS : S ∈ Ind hG.crossingGeometry) (hS' : IsDecomposition hn hP S)
    (hcb : CbProductsData hn hP hS') (q : GeoComponent hG.crossingGeometry S) :
    Omega1 hn hG hS q = cornerCoefficient hn hP S (geoComponentEquivGeneric hn hP S q) hS' := by
  rw [cornerCoefficient_eq_coeffAt]
  unfold Omega1
  rw [slot_eq_generic hn hP hG hS hS' q, groupedPoly_eq_cornerHomfly_of_cb hn hP hG hS hS' hcb q]

/-- The per-support summand of `X₁` is the per-support summand of lem:C-X1's selector form of `C`:
`wind(S) ∏_L Ω₁(S,L) = wind(S) ∏_Q c(Q)` (`Fintype.prod_equiv e`). -/
theorem X1_summand_eq_of_cb (hS : S ∈ Ind hG.crossingGeometry) (hS' : IsDecomposition hn hP S)
    (hcb : CbProductsData hn hP hS') :
    wind hG.crossingGeometry S * ∏ q : GeoComponent hG.crossingGeometry S, Omega1 hn hG hS q =
      SM.wind hn hP S * cornerProduct hn hP S hS' := by
  rw [wind_eq_generic hn hP hG hS']
  unfold cornerProduct
  congr 1
  exact Fintype.prod_equiv (geoComponentEquivGeneric hn hP S) _ _
    fun q => Omega1_eq_cornerCoefficient_of_cb hn hP hG hS hS' hcb q

end PerCarrier

/-! ## 3. The state sums: `X₁(P) = C(P)` (BRIDGE.md (17)) -/

/-- **BRIDGE.md (17)**, `C^SM(P) = X₁^CV(P)` for every SM-generic labelled `P`, FROM cb:products at every
decomposition of `P` (the hypothesis-shaped form; `SM.cb_products` discharges it in `Bridge/B4.lean`).  Route:
lem:C-X1's selector form (`SM.C_X1.selector_form`), `CV.Ind_eq_generic` (the two index sets), `sum_attach_congr`
(the attached sums), `X1_summand_eq_of_cb` (each summand). -/
theorem X1_eq_cornerStateSum_of_cb (hG : Generic P)
    (hcb : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S), CbProductsData hn hP hS) :
    X1 hn P hG = cornerStateSum hn hP := by
  rw [C_X1.selector_form n hn P hP]
  unfold X1
  refine sum_attach_congr (Ind_eq_generic hn hP hG.crossingGeometry) _ _ ?_
  intro S hS hS'
  exact X1_summand_eq_of_cb hn hP hG hS hS' (hcb S hS')

/-- The same at the bridge's own CV-generic proof `CV.generic_of_sm hn hP` (B1 (1)), the form Bridge:B4's field
`pointwise` prints. -/
theorem X1_generic_of_sm_eq_cornerStateSum_of_cb
    (hcb : ∀ (S : Finset (Crossing P)) (hS : IsDecomposition hn hP S), CbProductsData hn hP hS) :
    X1 hn P (generic_of_sm hn hP) = cornerStateSum hn hP :=
  X1_eq_cornerStateSum_of_cb hn hP (generic_of_sm hn hP) hcb

end CV
