import DaughterCarrierIntersection

set_option autoImplicit false
namespace DirectGLSSW.AuxiliaryCarrierChart
noncomputable section
open DirectGLSSW

/-- The numerator of the actual affine carrier intersection. -/
def lineNumerator (L M : CarrierLine) : PlanarPoint ℝ :=
  (M.2 * L.1.1 - L.2 * M.1.1, M.2 * L.1.2 - L.2 * M.1.2)

/-- Homogeneous determinant of three intersections, without division. -/
def carrierTripleNumerator (A B C D E F : CarrierLine) : ℝ :=
  (lineNumerator A B).1 *
      ((lineNumerator C D).2 * lineDenominator E F -
        lineDenominator C D * (lineNumerator E F).2) -
    (lineNumerator A B).2 *
      ((lineNumerator C D).1 * lineDenominator E F -
        lineDenominator C D * (lineNumerator E F).1) +
    lineDenominator A B *
      ((lineNumerator C D).1 * (lineNumerator E F).2 -
        (lineNumerator C D).2 * (lineNumerator E F).1)

theorem carrierTripleNumerator_eq_scaled_det (A B C D E F : CarrierLine)
    (hAB : lineDenominator A B ≠ 0)
    (hCD : lineDenominator C D ≠ 0)
    (hEF : lineDenominator E F ≠ 0) :
    carrierTripleNumerator A B C D E F =
      (lineDenominator A B * lineDenominator C D * lineDenominator E F) *
        planarDet (lineIntersection C D - lineIntersection A B)
          (lineIntersection E F - lineIntersection A B) := by
  simp only [carrierTripleNumerator, lineNumerator, lineIntersection,
    planarDet, Prod.fst_sub, Prod.snd_sub]
  field_simp [hAB, hCD, hEF]
  <;> ring

theorem carrierTripleNumerator_zero_iff (A B C D E F : CarrierLine)
    (hAB : lineDenominator A B ≠ 0)
    (hCD : lineDenominator C D ≠ 0)
    (hEF : lineDenominator E F ≠ 0) :
    carrierTripleNumerator A B C D E F = 0 ↔
      planarDet (lineIntersection C D - lineIntersection A B)
        (lineIntersection E F - lineIntersection A B) = 0 := by
  rw [carrierTripleNumerator_eq_scaled_det A B C D E F hAB hCD hEF]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero (mul_ne_zero hAB hCD) hEF))

theorem actual_daughter_triple_numerator_zero_iff
    {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root))) :
    let m := Fintype.card (DaughterFirstReturn.CornerCoord q hq.g2 S root)
    let prev : Fin m → Fin m := fun u => (cyclicSuccessorPerm m)⁻¹ u
    let L : Fin m → CarrierLine := fun u => polygonCarrierCoordinates q
      (DaughterFirstReturn.daughterCarrier q hq.g2 S root u)
    carrierTripleNumerator (L (prev i)) (L i) (L (prev j)) (L j)
        (L (prev k)) (L k) = 0 ↔
      planarDet
        (DaughterFirstReturn.daughterVertex q hq.g2 S root j -
          DaughterFirstReturn.daughterVertex q hq.g2 S root i)
        (DaughterFirstReturn.daughterVertex q hq.g2 S root k -
          DaughterFirstReturn.daughterVertex q hq.g2 S root i) = 0 := by
  dsimp only
  have hi := DaughterCarrierIntersection.actual_daughter_carrier_intersection q hq S root hroot i
  have hj := DaughterCarrierIntersection.actual_daughter_carrier_intersection q hq S root hroot j
  have hk := DaughterCarrierIntersection.actual_daughter_carrier_intersection q hq S root hroot k
  dsimp only at hi hj hk
  rw [hi.2.2.2, hj.2.2.2, hk.2.2.2]
  exact carrierTripleNumerator_zero_iff _ _ _ _ _ _ hi.2.2.1 hj.2.2.1 hk.2.2.1

end
end DirectGLSSW.AuxiliaryCarrierChart




