import DaughterClosedContainment
import LocalCarrierPolygonRecovery
import DirectGLSSW.DaughterTurns

set_option autoImplicit false
namespace DirectGLSSW.DaughterCarrierIntersection
noncomputable section
open DirectGLSSW

theorem actual_daughter_carrier_intersection
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root))) :
    let m := Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)
    let prev : Fin m := (cyclicSuccessorPerm m)⁻¹ i
    let L : Fin m → AuxiliaryCarrierChart.CarrierLine := fun j =>
      AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root j)
    AuxiliaryCarrierChart.lineValue (L i)
        (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 ∧
      AuxiliaryCarrierChart.lineValue (L prev)
        (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 ∧
      AuxiliaryCarrierChart.lineDenominator (L prev) (L i) ≠ 0 ∧
      DaughterFirstReturn.daughterVertex q hq.g2 S root i =
        AuxiliaryCarrierChart.lineIntersection (L prev) (L i) := by
  classical
  change
    AuxiliaryCarrierChart.lineValue
      (AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root i))
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 ∧
    AuxiliaryCarrierChart.lineValue
      (AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root
          ((cyclicSuccessorPerm
            (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i)))
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 ∧
    AuxiliaryCarrierChart.lineDenominator
      (AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root
          ((cyclicSuccessorPerm
            (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i)))
      (AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root i)) ≠ 0 ∧
    DaughterFirstReturn.daughterVertex q hq.g2 S root i =
      AuxiliaryCarrierChart.lineIntersection
        (AuxiliaryCarrierChart.polygonCarrierCoordinates q
          (DaughterFirstReturn.daughterCarrier q hq.g2 S root
            ((cyclicSuccessorPerm
              (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)))⁻¹ i)))
        (AuxiliaryCarrierChart.polygonCarrierCoordinates q
          (DaughterFirstReturn.daughterCarrier q hq.g2 S root i))
  let m := Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)
  let prev : Fin m := (cyclicSuccessorPerm m)⁻¹ i
  let L : Fin m → AuxiliaryCarrierChart.CarrierLine := fun j =>
    AuxiliaryCarrierChart.polygonCarrierCoordinates q
      (DaughterFirstReturn.daughterCarrier q hq.g2 S root j)
  change AuxiliaryCarrierChart.lineValue (L i)
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 ∧
    AuxiliaryCarrierChart.lineValue (L prev)
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 ∧
    AuxiliaryCarrierChart.lineDenominator (L prev) (L i) ≠ 0 ∧
    DaughterFirstReturn.daughterVertex q hq.g2 S root i =
      AuxiliaryCarrierChart.lineIntersection (L prev) (L i)
  have hprev_succ : cyclicSuccessor prev = i := by
    change cyclicSuccessorPerm m ((cyclicSuccessorPerm m)⁻¹ i) = i
    exact Equiv.apply_symm_apply (cyclicSuccessorPerm m) i
  have hline_affine (e : Fin n) (r : ℝ) :
      AuxiliaryCarrierChart.lineValue
        (AuxiliaryCarrierChart.polygonCarrierCoordinates q e)
        (affinePoint (q e) (q (cyclicSuccessor e)) r) = 0 := by
    simp only [AuxiliaryCarrierChart.lineValue,
      AuxiliaryCarrierChart.polygonCarrierCoordinates, cyclicTangent, affinePoint]
    simp only [planarDet, Prod.fst_sub, Prod.snd_sub]
    ring
  obtain ⟨s, t, hs0, hst, ht1, hpoint_i, hpoint_next⟩ :=
    DaughterClosedContainment.daughterSide_endpoint_parameters
      q hq.g2 S hq.size_ge_three root hroot i
  obtain ⟨sp, tp, hsp0, hspt, hpt1, hpoint_prev, hpoint_prev_next⟩ :=
    DaughterClosedContainment.daughterSide_endpoint_parameters
      q hq.g2 S hq.size_ge_three root hroot prev
  rw [hprev_succ] at hpoint_prev_next
  have hline_i : AuxiliaryCarrierChart.lineValue (L i)
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 := by
    change AuxiliaryCarrierChart.lineValue
      (AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root i))
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0
    rw [hpoint_i]
    exact hline_affine (DaughterFirstReturn.daughterCarrier q hq.g2 S root i) s
  have hline_prev : AuxiliaryCarrierChart.lineValue (L prev)
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 := by
    change AuxiliaryCarrierChart.lineValue
      (AuxiliaryCarrierChart.polygonCarrierCoordinates q
        (DaughterFirstReturn.daughterCarrier q hq.g2 S root prev))
      (DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0
    rw [hpoint_prev_next]
    exact hline_affine (DaughterFirstReturn.daughterCarrier q hq.g2 S root prev) tp
  have hturn := DaughterTurns.daughterTurn_ne_zero
      q hq.g2 S hq.size_ge_three hq.g1 root hroot i
  obtain ⟨hscale_prev_pos, hscale_prev⟩ :=
    DaughterFirstReturn.daughterSide_positive_multiple
      q hq.g2 S hq.size_ge_three root hroot prev
  obtain ⟨hscale_i_pos, hscale_i⟩ :=
    DaughterFirstReturn.daughterSide_positive_multiple
      q hq.g2 S hq.size_ge_three root hroot i
  have hscale_prev' : DaughterFirstReturn.daughterSideVector q hq.g2 S root prev =
      DaughterFirstReturn.daughterSideScale q hq.g2 S root
        (DaughterFirstReturn.cornerEnumeration q hq.g2 S root prev) •
      cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 S root prev) := by
    simpa only [DaughterFirstReturn.daughterCarrier] using hscale_prev
  have hscale_i' : DaughterFirstReturn.daughterSideVector q hq.g2 S root i =
      DaughterFirstReturn.daughterSideScale q hq.g2 S root
        (DaughterFirstReturn.cornerEnumeration q hq.g2 S root i) •
      cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 S root i) := by
    simpa only [DaughterFirstReturn.daughterCarrier] using hscale_i
  have hdet_smul (u v : PlanarPoint ℝ) (a b : ℝ) :
      planarDet (a • u) (b • v) = a * b * planarDet u v := by
    simp [planarDet, smul_eq_mul]
    ring
  have hbase : planarDet
      (cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 S root prev))
      (cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 S root i)) ≠ 0 := by
    intro hz
    have hscaled : planarDet
        (DaughterFirstReturn.daughterSideVector q hq.g2 S root prev)
        (DaughterFirstReturn.daughterSideVector q hq.g2 S root i) = 0 := by
      rw [hscale_prev', hscale_i', hdet_smul, hz]
      ring
    exact hturn hscaled
  have hdenominator : AuxiliaryCarrierChart.lineDenominator (L prev) (L i) ≠ 0 := by
    change planarDet
      (cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 S root prev))
      (cyclicTangent q (DaughterFirstReturn.daughterCarrier q hq.g2 S root i)) ≠ 0
    exact hbase
  refine ⟨hline_i, hline_prev, hdenominator, ?_⟩
  exact AuxiliaryCarrierChart.lineIntersection_unique (L prev) (L i)
    (DaughterFirstReturn.daughterVertex q hq.g2 S root i)
    hdenominator hline_prev hline_i

end
end DirectGLSSW.DaughterCarrierIntersection


