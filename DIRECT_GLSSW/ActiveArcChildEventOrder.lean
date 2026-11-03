import ActiveArcChildRetainedRange

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits FiniteCycleOrder SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)

theorem childEventMap_edgeTag (x : PolygonEvent (child q hR c hc.1 hcut))
    (hx : x≠Sum.inl 0) :
    edgeTag q (childEventMap q hR c hc hcut x)=
      (polygonEventEdge (child q hR c hc.1 hcut) x).val := by
  cases x with
  | inl i =>
    have hi : i≠0 := fun he => hx (congrArg Sum.inl he)
    simp only [childEventMap,if_neg hi,edgeTag,childVertex,polygonEventEdge]
  | inr v =>
    change (visitEdge q (childVisitMap q hR c hc.1 hcut v)).val=_
    rw [childVisitMap_edge]
    rfl

theorem childEventMap_parameter (x : PolygonEvent (child q hR c hc.1 hcut))
    (hx : x≠Sum.inl 0) :
    parameter q (childEventMap q hR c hc hcut x)=
      childOffset q c (polygonEventEdge (child q hR c hc.1 hcut) x)+
      childScale q c (polygonEventEdge (child q hR c hc.1 hcut) x)*
        polygonEventParameter (child q hR c hc.1 hcut) x := by
  cases x with
  | inl i =>
    have hi : i≠0 := fun he => hx (congrArg Sum.inl he)
    simp [childEventMap,hi,parameter,childOffset,polygonEventEdge,polygonEventParameter]
  | inr v => exact childVisitMap_parameter q hR c hc.1 hcut v

/-- Away from the zero anchor, the child-to-interval map is increasing. -/
theorem childEventMap_lt_nonzero (x y : PolygonEvent (child q hR c hc.1 hcut))
    (hx : x≠Sum.inl 0) (hy : y≠Sum.inl 0) :
    (eventOrder q hR.noTriple).lt (childEventMap q hR c hc hcut x) (childEventMap q hR c hc hcut y) ↔
      (polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)).lt x y := by
  rw [event_lt_iff,polygonEvent_lt_iff,childEventMap_edgeTag q hR c hc hcut x hx,
    childEventMap_edgeTag q hR c hc hcut y hy,childEventMap_parameter q hR c hc hcut x hx,
    childEventMap_parameter q hR c hc hcut y hy]
  simp only [Fin.val_inj]
  by_cases he : polygonEventEdge (child q hR c hc.1 hcut) x=polygonEventEdge (child q hR c hc.1 hcut) y
  · rw [he]
    simp only [lt_self_iff_false,true_and,false_or,add_lt_add_iff_left,
      mul_lt_mul_left (childScale_pos q c _)]
  · simp only [he,false_and,or_false]
    rfl

/-- The zero anchor is the actual minimum of the child event order. -/
theorem child_zero_le (x : PolygonEvent (child q hR c hc.1 hcut)) :
    (polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)).le (Sum.inl 0) x := by
  letI := polygonEventOrder (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut)
  apply le_of_not_gt
  intro hh
  have hh := (polygonEvent_lt_iff (child q hR c hc.1 hcut) (child_noTriple q hR c hc.1 hcut) x (Sum.inl 0)).mp hh
  cases x with
  | inl i =>
    rcases hh with he|⟨_,hp⟩
    · exact (not_lt_of_ge (Fin.zero_le i)) he
    · exact (lt_irrefl (0 : ℝ)) hp
  | inr v =>
    rcases hh with he|⟨he,hp⟩
    · exact (not_lt_of_ge (Fin.zero_le _)) he
    · exact (not_lt_of_ge (le_of_lt (crossingVisitParameter_spec _ v).1)) hp

end DirectGLSSW.ActiveArc.CompatibleWords
