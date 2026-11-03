import MovedSuffixOrientation
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open PolygonDrawingBridge PolygonDrawing SmoothingCornerGeometry EventSegmentGeometry
open ActiveArc.ExposedChart ExposedOpenPrimitive
attribute [local instance] Classical.propDecidable

section Boundary
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
    {t : MarkedParentState}
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (A : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 A))
    (a b : ℕ) (hs : a+b=n) (θ : ℝ)
    (hcarrier : (polygonEventEdge q ((eventFin q).symm (h.boundaryOrigin A B))).val=a+1)
    (hlo : polygonEventParameter q ((eventFin q).symm (h.boundaryOrigin A B)) ≤ θ)
    (hhi : θ < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three
      ((eventFin q).symm (h.boundaryOrigin A B)))
    (c : ActiveArc.Crossing (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ))

/-- Actual current badness is the sign of the arbitrary physical moved suffix,
not a sign asserted only at a specially selected historical cursor. -/
theorem boundary_physical_bad_iff :
    badAt t.2.1 (boundaryPhysicalCrossingEquiv q hq he h A B a b hs θ hcarrier hlo hhi c).val ↔
      ¬ 0 < planarDet
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ c.val.1.succ-
          ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ c.val.1.castSucc)
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ c.val.2.succ-
          ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ c.val.2.castSucc) := by
  have hb := boundaryPhysicalCrossingEquiv_bad_iff q hq he h A B a b hs θ hcarrier hlo hhi c
  let h0 := le_trans (polygonEventParameter_bounds q ((eventFin q).symm (h.boundaryOrigin A B))).1 hlo
  let h1 := lt_of_lt_of_le hhi (polygonEventSuccessorTerminalParameter_bounds q hq.g2 hq.size_ge_three
    ((eventFin q).symm (h.boundaryOrigin A B))).2
  let z := (ActiveArc.Split.suffixWordCrossingEquiv (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ h0 h1 c).val
  have ho := original_positive_bad_iff q hq (exposedCrossingEquiv q 0 hq he z)
  have hd := moved_suffix_det_pos_iff q hq he a b hs θ h0 h1 c
  exact hb.trans (ho.trans (not_congr hd).symm)

theorem boundary_physical_over_left_iff :
    crossingOver (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ)
      (ActiveArc.polygonCrossingOfArc
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) c)=
      (ActiveArc.polygonCrossingOfArc
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) c).val.1 ↔
    ¬ badAt t.2.1 (boundaryPhysicalCrossingEquiv q hq he h A B a b hs θ hcarrier hlo hhi c).val := by
  have hn := not_congr (boundary_physical_bad_iff q hq he h A B a b hs θ hcarrier hlo hhi c)
  simp only [not_not] at hn
  exact (open_arc_over_left_iff _ c).trans hn.symm

theorem boundary_physical_under_left_iff :
    crossingUnder (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ)
      (ActiveArc.polygonCrossingOfArc
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) c)=
      (ActiveArc.polygonCrossingOfArc
        (ActiveArc.Cursor.moveStart (ActiveArc.Split.suffixWord (cutArc q 0) a b hs) θ) c).val.1 ↔
    badAt t.2.1 (boundaryPhysicalCrossingEquiv q hq he h A B a b hs θ hcarrier hlo hhi c).val := by
  exact (open_arc_under_left_iff _ c).trans
    (boundary_physical_bad_iff q hq he h A B a b hs θ hcarrier hlo hhi c).symm
end Boundary

section Cursor
variable {n m : ℕ} {q : Fin (n+2) → PlanarPoint ℝ} {hq : CyclicGeneric q}
    {p : Fin (m+2) → PlanarPoint ℝ} {t : MarkedParentState}
    {h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t}
    (G : GeometricCursor q hq p t h) (he : LeftExposed q 0) (c : ActiveArc.Crossing p)

/-- Every actual geometric cursor has its physical/current sign relation. -/
theorem GeometricCursor.crossing_bad_iff_not_positive :
    badAt t.2.1 ((G.crossingEquiv he) c).val ↔
      ¬ 0 < planarDet (p c.val.1.succ-p c.val.1.castSucc) (p c.val.2.succ-p c.val.2.castSucc) := by
  rcases G with ⟨A,B,a,hs,θ,h0,h1,hcarrier,hlo,hhi,hword⟩
  subst p
  exact boundary_physical_bad_iff q hq he h A B a m hs θ hcarrier hlo hhi c

theorem GeometricCursor.over_left_iff_not_bad :
    crossingOver p (ActiveArc.polygonCrossingOfArc p c)=(ActiveArc.polygonCrossingOfArc p c).val.1 ↔
      ¬ badAt t.2.1 ((G.crossingEquiv he) c).val := by
  have hn := not_congr (G.crossing_bad_iff_not_positive he c)
  simp only [not_not] at hn
  exact (open_arc_over_left_iff p c).trans hn.symm

theorem GeometricCursor.under_left_iff_bad :
    crossingUnder p (ActiveArc.polygonCrossingOfArc p c)=(ActiveArc.polygonCrossingOfArc p c).val.1 ↔
      badAt t.2.1 ((G.crossingEquiv he) c).val :=
  (open_arc_under_left_iff p c).trans (G.crossing_bad_iff_not_positive he c).symm

/-- Over encounters at arbitrary actual cursor parameters are good. -/
theorem GeometricCursor.over_not_bad
    (hov : crossingOver p (ActiveArc.polygonCrossingOfArc p c)=(ActiveArc.polygonCrossingOfArc p c).val.1) :
    ¬ badAt t.2.1 ((G.crossingEquiv he) c).val :=
  (G.over_left_iff_not_bad he c).mp hov

/-- Under encounters at arbitrary actual cursor parameters are bad. -/
theorem GeometricCursor.under_bad
    (hu : crossingUnder p (ActiveArc.polygonCrossingOfArc p c)=(ActiveArc.polygonCrossingOfArc p c).val.1) :
    badAt t.2.1 ((G.crossingEquiv he) c).val :=
  (G.under_left_iff_bad he c).mp hu
end Cursor









end DirectGLSSW.HOMFLY.PhysicalCursorComparison
