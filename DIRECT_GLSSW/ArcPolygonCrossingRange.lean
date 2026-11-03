import ArcPolygonVisitParameters

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

theorem polygonCrossingOfArc_injective : Function.Injective (polygonCrossingOfArc q) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun z : PolygonCrossing q => z.val.1.val) h
  · apply Fin.ext
    exact congrArg (fun z : PolygonCrossing q => z.val.2.val) h

private theorem cyclicSuccessor_castSucc (e : Fin (n+1)) :
    cyclicSuccessor e.castSucc = e.succ := by
  apply Fin.ext
  change (e.val+1+0)%(n+2)=e.val+1
  exact Nat.mod_eq_of_lt (by omega)

/-- The physical open-arc crossing inclusion exhausts precisely the polygon
crossings avoiding the additional last edge. -/
theorem polygonCrossingOfArc_range (d : PolygonCrossing q) :
    (∃ e : Crossing q, polygonCrossingOfArc q e=d) ↔ d.val.2.val<n+1 := by
  constructor
  · rintro ⟨e,rfl⟩;exact e.val.2.isLt
  · intro hd
    let l : Fin (n+1) := ⟨d.val.1.val,lt_trans d.property.1 hd⟩
    let r : Fin (n+1) := ⟨d.val.2.val,hd⟩
    have hl : l.castSucc=d.val.1 := Fin.ext rfl
    have hr : r.castSucc=d.val.2 := Fin.ext rfl
    obtain ⟨x,hx,hy⟩ := d.property.2
    have hx' : edgeInterior q l x := by
      change OnOpenSegment (q l.castSucc) (q l.succ) x
      rw [←cyclicSuccessor_castSucc,hl]
      exact hx
    have hy' : edgeInterior q r x := by
      change OnOpenSegment (q r.castSucc) (q r.succ) x
      rw [←cyclicSuccessor_castSucc,hr]
      exact hy
    let e : Crossing q := ⟨(l,r),d.property.1,x,hx',hy'⟩
    refine ⟨e,?_⟩
    apply Subtype.ext
    exact Prod.ext hl hr
end DirectGLSSW.ActiveArc
