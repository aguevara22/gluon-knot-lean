import GeometricCursorCrossingEquiv
import FirstPhysicalEvent
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

/-- A physical open crossing uses the same two nonclosing cyclic tangents. -/
theorem open_arc_crossing_det {m : ℕ} (p : Fin (m+2) → PlanarPoint ℝ) (d : ActiveArc.Crossing p) :
    planarDet (cyclicTangent p (ActiveArc.polygonCrossingOfArc p d).val.1)
      (cyclicTangent p (ActiveArc.polygonCrossingOfArc p d).val.2) =
    planarDet (p d.val.1.succ-p d.val.1.castSucc) (p d.val.2.succ-p d.val.2.castSucc) := by
  have hs (e : Fin (m+1)) : cyclicSuccessor e.castSucc=e.succ := by
    apply Fin.ext
    change (e.val+1+0)%(m+2)=e.val+1
    exact Nat.mod_eq_of_lt (by have := e.isLt;omega)
  change planarDet (cyclicTangent p d.val.1.castSucc) (cyclicTangent p d.val.2.castSucc)=_
  simp only [cyclicTangent,hs]

theorem open_arc_over_left_iff {m : ℕ} (p : Fin (m+2) → PlanarPoint ℝ) (d : ActiveArc.Crossing p) :
    crossingOver p (ActiveArc.polygonCrossingOfArc p d)=(ActiveArc.polygonCrossingOfArc p d).val.1 ↔
      0 < planarDet (p d.val.1.succ-p d.val.1.castSucc) (p d.val.2.succ-p d.val.2.castSucc) := by
  rw [← open_arc_crossing_det p d]
  unfold crossingOver
  by_cases hp : 0 < planarDet (cyclicTangent p (ActiveArc.polygonCrossingOfArc p d).val.1)
    (cyclicTangent p (ActiveArc.polygonCrossingOfArc p d).val.2)
  all_goals simp [hp,Ne.symm (crossing_edges_ne p (ActiveArc.polygonCrossingOfArc p d))]

theorem open_arc_under_left_iff {m : ℕ} (p : Fin (m+2) → PlanarPoint ℝ) (d : ActiveArc.Crossing p) :
    crossingUnder p (ActiveArc.polygonCrossingOfArc p d)=(ActiveArc.polygonCrossingOfArc p d).val.1 ↔
      ¬ 0 < planarDet (p d.val.1.succ-p d.val.1.castSucc) (p d.val.2.succ-p d.val.2.castSucc) := by
  rw [← open_arc_crossing_det p d]
  unfold crossingUnder
  by_cases hp : 0 < planarDet (cyclicTangent p (ActiveArc.polygonCrossingOfArc p d).val.1)
    (cyclicTangent p (ActiveArc.polygonCrossingOfArc p d).val.2)
  all_goals simp [hp,Ne.symm (crossing_edges_ne p (ActiveArc.polygonCrossingOfArc p d))]

/-- The initial rooted positive diagram is bad precisely when the ordered
original carrier determinant is not positive. No selected bad cursor is used. -/
theorem original_positive_bad_iff {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (d : PolygonCrossing q) :
    badAt (initialAnchorTraversal q hq) (crossingFin q d) ↔
      ¬ 0 < planarDet (cyclicTangent q d.val.1) (cyclicTangent q d.val.2) := by
  unfold badAt
  rw [initialAnchorTraversal_firstVisitedBranch q hq d,positivePolygonEventDiagram_overBranch q hq d]
  by_cases hp : 0 < planarDet (cyclicTangent q d.val.1) (cyclicTangent q d.val.2)
  all_goals simp [hp]

/-- Every actual moved-suffix crossing keeps the ordered orientation of its
literal original polygon crossing: both tangent scales are positive. -/
theorem moved_suffix_det_pos_iff {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (he : LeftExposed q 0) (a b : ℕ) (hs : a+b=n)
    (θ : ℝ) (h0 : 0≤θ) (h1 : θ<1)
    (d : ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ)) :
    (0 < planarDet
      (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ d.val.1.succ-
        ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ d.val.1.castSucc)
      (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ d.val.2.succ-
        ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ d.val.2.castSucc)) ↔
    (let z := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ h0 h1 d).val
     let c := exposedCrossingEquiv q 0 hq he z
     0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)) := by
  let cut := cutArc q 0
  let w := ActiveArc.Split.suffixWord cut a b hs
  let z := (ActiveArc.Split.suffixWordCrossingEquiv cut (cutArc_regular q 0 hq) a b hs θ h0 h1 d).val
  let c := exposedCrossingEquiv q 0 hq he z
  have hzL : z.val.1.val=a+d.val.1.val :=
    ActiveArc.Split.suffixWordCrossingEquiv_left_label cut (cutArc_regular q 0 hq) a b hs θ h0 h1 d
  have hzR : z.val.2.val=a+d.val.2.val :=
    ActiveArc.Split.suffixWordCrossingEquiv_right_label cut (cutArc_regular q 0 hq) a b hs θ h0 h1 d
  have heL : c.val.1.val=a+d.val.1.val+1 := by
    exact (exposedCrossing_firstEdge q hq he z).trans (congrArg (fun k : ℕ => k+1) hzL)
  have hsecond : c.val.2.val=z.val.2.val+1 := by
    have hr := crossingEquiv_visit_edge q 0 hq z true
    change edgeLabel (0 : Fin (n+2)) z.val.2=c.val.1 ∨
      edgeLabel (0 : Fin (n+2)) z.val.2=c.val.2 at hr
    rcases hr with hb|hg
    · have hv := congrArg Fin.val hb
      rw [zero_edgeLabel_val] at hv
      have hfirst := exposedCrossing_firstEdge q hq he z
      change c.val.1.val=z.val.1.val+1 at hfirst
      rw [hfirst] at hv
      have hz := z.property.1
      change z.val.1.val<z.val.2.val at hz
      omega
    · have hv := congrArg Fin.val hg
      rw [zero_edgeLabel_val] at hv
      exact hv.symm
  have heR : c.val.2.val=a+d.val.2.val+1 := by
    exact hsecond.trans (congrArg (fun k : ℕ => k+1) hzR)
  have hcutL : edgeLabel (0 : Fin (n+2))
      (⟨a+d.val.1.val,by have := d.val.1.isLt;omega⟩ : Fin (n+1))=c.val.1 := by
    apply Fin.ext
    rw [zero_edgeLabel_val]
    exact heL.symm
  have hcutR : edgeLabel (0 : Fin (n+2))
      (⟨a+d.val.2.val,by have := d.val.2.isLt;omega⟩ : Fin (n+1))=c.val.2 := by
    apply Fin.ext
    rw [zero_edgeLabel_val]
    exact heR.symm
  have htanL : w d.val.1.succ-w d.val.1.castSucc=cyclicTangent q c.val.1 := by
    rw [← hcutL]
    change cut ⟨a+d.val.1.val+1,by have := d.val.1.isLt;omega⟩-
      cut ⟨a+d.val.1.val,by have := d.val.1.isLt;omega⟩=_
    exact cut_tangent q 0 ⟨a+d.val.1.val,by have := d.val.1.isLt;omega⟩
  have htanR : w d.val.2.succ-w d.val.2.castSucc=cyclicTangent q c.val.2 := by
    rw [← hcutR]
    change cut ⟨a+d.val.2.val+1,by have := d.val.2.isLt;omega⟩-
      cut ⟨a+d.val.2.val,by have := d.val.2.isLt;omega⟩=_
    exact cut_tangent q 0 ⟨a+d.val.2.val,by have := d.val.2.isLt;omega⟩
  have hd := ActiveArc.Cursor.det_tangent_moveStart w θ d.val.1 d.val.2
  rw [htanL,htanR] at hd
  have hscale (e : Fin (b+1)) : 0 < ActiveArc.Cursor.tangentScale θ e := by
    unfold ActiveArc.Cursor.tangentScale
    split_ifs
    · exact sub_pos.mpr h1
    · norm_num
  change (0 < planarDet (ActiveArc.Cursor.moveStart w θ d.val.1.succ-ActiveArc.Cursor.moveStart w θ d.val.1.castSucc)
      (ActiveArc.Cursor.moveStart w θ d.val.2.succ-ActiveArc.Cursor.moveStart w θ d.val.2.castSucc)) ↔
    0 < planarDet (cyclicTangent q c.val.1) (cyclicTangent q c.val.2)
  rw [hd]
  exact mul_pos_iff_of_pos_left (mul_pos (hscale d.val.1) (hscale d.val.2))






end DirectGLSSW.HOMFLY.PhysicalCursorComparison
