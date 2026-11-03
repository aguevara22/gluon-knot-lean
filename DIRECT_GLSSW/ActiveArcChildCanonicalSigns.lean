import ActiveArcChildTangentSign
import ActiveArcPositiveFirstCrossing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

private theorem tangent_castSucc {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ)
    (e : Fin (n+1)) : cyclicTangent p e.castSucc=p e.succ-p e.castSucc := by
  unfold cyclicTangent
  congr 1
  congr 1
  apply Fin.ext
  change (e.val+1+0)%(n+2)=e.val+1
  exact Nat.mod_eq_of_lt (by omega)

/-- The actual child crossing's two ordered tangents have the original
crossing determinant multiplied by the two positive shortening factors. -/
theorem childCrossing_orderedDet
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    planarDet (cyclicTangent (child q hR c hfirst hcut) d.val.1)
      (cyclicTangent (child q hR c hfirst hcut) d.val.2) =
      (childScale q c d.val.1*childScale q c d.val.2)*
        planarDet
          (cyclicTangent q (polygonCrossingOfArc q
            (childCrossingToOriginal q hR c hfirst hcut d)).val.1)
          (cyclicTangent q (polygonCrossingOfArc q
            (childCrossingToOriginal q hR c hfirst hcut d)).val.2) := by
  change _ = (childScale q c d.val.1*childScale q c d.val.2)*
    planarDet (cyclicTangent q (childEdge (b:=b) d.val.1).castSucc)
      (cyclicTangent q (childEdge (b:=b) d.val.2).castSucc)
  rw [tangent_castSucc,tangent_castSucc]
  exact child_cyclicTangent_det q hR c hfirst hcut d.val.1 d.val.2

/-- Original physical regularity rules out the zero-sign fallback at an
actual child crossing; no child G1 certificate is required. -/
theorem childCrossing_orderedDet_ne_zero
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    planarDet (cyclicTangent (child q hR c hfirst hcut) d.val.1)
      (cyclicTangent (child q hR c hfirst hcut) d.val.2) ≠ 0 := by
  let dOld := childCrossingToOriginal q hR c hfirst hcut d
  have hd := hR.transverse dOld.val.1 dOld.val.2 (ne_of_lt dOld.property.1)
    (crossingPoint q dOld) (crossingPoint_mem q dOld).1 (crossingPoint_mem q dOld).2
  rw [child_cyclicTangent_det q hR c hfirst hcut]
  exact mul_ne_zero
    (ne_of_gt (mul_pos (childScale_pos q c d.val.1) (childScale_pos q c d.val.2))) hd

theorem childCrossing_orderedDet_pos_iff
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    0<planarDet (cyclicTangent (child q hR c hfirst hcut) d.val.1)
      (cyclicTangent (child q hR c hfirst hcut) d.val.2) ↔
      0<planarDet
        (cyclicTangent q (polygonCrossingOfArc q
          (childCrossingToOriginal q hR c hfirst hcut d)).val.1)
        (cyclicTangent q (polygonCrossingOfArc q
          (childCrossingToOriginal q hR c hfirst hcut d)).val.2) := by
  rw [childCrossing_orderedDet q hR c hfirst hcut]
  exact mul_pos_iff_of_pos_left
    (mul_pos (childScale_pos q c d.val.1) (childScale_pos q c d.val.2))

theorem childCrossing_orderedDet_sign
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    scalarSignValue (planarDet
      (cyclicTangent (child q hR c hfirst hcut) d.val.1)
      (cyclicTangent (child q hR c hfirst hcut) d.val.2)) =
      scalarSignValue (planarDet
        (cyclicTangent q (polygonCrossingOfArc q
          (childCrossingToOriginal q hR c hfirst hcut d)).val.1)
        (cyclicTangent q (polygonCrossingOfArc q
          (childCrossingToOriginal q hR c hfirst hcut d)).val.2)) := by
  change _ = scalarSignValue (planarDet
    (cyclicTangent q (childEdge (b:=b) d.val.1).castSucc)
    (cyclicTangent q (childEdge (b:=b) d.val.2).castSucc))
  rw [tangent_castSucc,tangent_castSucc]
  exact child_cyclicTangent_det_sign q hR c hfirst hcut d.val.1 d.val.2

/-- Canonical positive-lift overstrand, mapped by its actual original edge label. -/
theorem childCrossing_crossingOver
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    (childEdge (b:=b) (crossingOver (child q hR c hfirst hcut) d)).castSucc =
      crossingOver q (polygonCrossingOfArc q
        (childCrossingToOriginal q hR c hfirst hcut d)) := by
  unfold crossingOver
  simp only [childCrossing_orderedDet_pos_iff q hR c hfirst hcut d]
  split_ifs <;> rfl

/-- Canonical positive-lift understrand, mapped by its actual original edge label. -/
theorem childCrossing_crossingUnder
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    (childEdge (b:=b) (crossingUnder (child q hR c hfirst hcut) d)).castSucc =
      crossingUnder q (polygonCrossingOfArc q
        (childCrossingToOriginal q hR c hfirst hcut d)) := by
  unfold crossingUnder
  simp only [childCrossing_orderedDet_pos_iff q hR c hfirst hcut d]
  split_ifs <;> rfl

/-- Typed diagram corollary: the two supplied certificates are needed only
for constructing the actual positive PL event diagrams. No existence claim. -/
theorem childCrossing_positiveDiagram_overBranch
    (hQ : CyclicGeneric q)
    (hChild : CyclicGeneric (child q hR c hfirst hcut))
    (d : PolygonCrossing (child q hR c hfirst hcut)) :
    (HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram
      (child q hR c hfirst hcut) hChild).overBranch
        (HOMFLY.PolygonDrawingBridge.crossingFin (child q hR c hfirst hcut) d) =
      (HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram q hQ).overBranch
        (HOMFLY.PolygonDrawingBridge.crossingFin q (polygonCrossingOfArc q
          (childCrossingToOriginal q hR c hfirst hcut d))) := by
  rw [HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_overBranch,
    HOMFLY.PolygonDrawingBridge.positivePolygonEventDiagram_overBranch]
  simp only [childCrossing_orderedDet_pos_iff q hR c hfirst hcut d]

end DirectGLSSW.ActiveArc.Split
