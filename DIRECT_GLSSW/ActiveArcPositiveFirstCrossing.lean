import ActiveArcGammaMBoundaryTransport
import PositiveLiftFirstEncounter

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc

private theorem cyclicSuccessor_castSucc {n : ℕ} (e : Fin (n+1)) :
    cyclicSuccessor e.castSucc = e.succ := by
  apply Fin.ext
  change (e.val+1+0)%(n+2)=e.val+1
  exact Nat.mod_eq_of_lt (by omega)

private theorem polygonInterior_of_arc {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+1)) (x : PlanarPoint ℝ) (hx : edgeInterior q e x) :
    DirectGLSSW.edgeInterior q e.castSucc x := by
  simpa only [DirectGLSSW.edgeInterior, edgeInterior, cyclicSuccessor_castSucc] using hx

/-- Embed the actual arc crossing in its cyclic closure using the same two
physical edges. The additional closing edge is not used. -/
def polygonCrossingOfArc {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (c : Crossing q) :
    PolygonCrossing q :=
  ⟨(c.val.1.castSucc,c.val.2.castSucc), c.property.1,
    crossingPoint q c,
    polygonInterior_of_arc q _ _ (crossingPoint_mem q c).1,
    polygonInterior_of_arc q _ _ (crossingPoint_mem q c).2⟩

/-- Actual first-crossing sign and point, with the canonical polygon encounter
order and positive-lift over/under relation. -/
theorem polygonCrossingOfArc_first_sign {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (c : Crossing q) (hc : Cursor.FirstCrossing q c) (hG1 : cyclicNoncollinear q) :
    let C := polygonCrossingOfArc q c
    C.val.1.val=0 ∧ C.val.2.val=c.val.2.val ∧
    DirectGLSSW.crossingPoint q C=crossingPoint q c ∧
    toLex (polygonEventKey q (Sum.inr (C,false))) <
      toLex (polygonEventKey q (Sum.inr (C,true))) ∧
    (scalarSignValue (planarDet (q 1-q 0)
      (q c.val.2.succ-q c.val.2.castSucc))=1 ↔ crossingOver q C=C.val.1) ∧
    (scalarSignValue (planarDet (q 1-q 0)
      (q c.val.2.succ-q c.val.2.castSucc))=-1 ↔ crossingUnder q C=C.val.1) := by
  have hsize : 3≤n+2 := by have hlt:=c.property.1; have hbound:=c.val.2.isLt; omega
  have hfirst : c.val.1=0 := hc.1
  have hsign := HOMFLY.PolygonDrawingBridge.polygonCrossing_firstVisit_overUnder_sign
    q hsize hG1 (polygonCrossingOfArc q c)
  have hdet : planarDet (cyclicTangent q (polygonCrossingOfArc q c).val.1)
      (cyclicTangent q (polygonCrossingOfArc q c).val.2) =
      planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc) := by
    simp only [polygonCrossingOfArc, cyclicTangent, cyclicSuccessor_castSucc]
    rw [hfirst]
    rfl
  rw [hdet] at hsign
  refine ⟨congrArg Fin.val hc.1,rfl,?_,?_,hsign⟩
  · exact (DirectGLSSW.crossingPoint_eq_of_mem hsize q hG1 (polygonCrossingOfArc q c)
      (crossingPoint q c) (polygonInterior_of_arc q _ _ (crossingPoint_mem q c).1)
      (polygonInterior_of_arc q _ _ (crossingPoint_mem q c).2)).symm
  · exact HOMFLY.PolygonDrawingBridge.polygonCrossing_lowerVisit_key_before_upperVisit q _



end DirectGLSSW.ActiveArc
