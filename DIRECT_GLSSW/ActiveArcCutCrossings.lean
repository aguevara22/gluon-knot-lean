import ActiveArcCutGeometry
import ExposedEdgeGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
open DirectGLSSW PrimitiveEdgeGrouping ExposedOpenPrimitive
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (e : Fin (n+2))
variable (hq : CyclicGeneric q)

abbrev OffCrossing := {c : PolygonCrossing q // ¬Incident q e c}

include hq in
/-- Every physical cut crossing determines an original off-edge crossing at the same point. -/
theorem exists_offCrossing_at (c : ActiveArc.Crossing (cutArc q e)) :
    ∃ d : OffCrossing q e, DirectGLSSW.crossingPoint q d.val=ActiveArc.crossingPoint (cutArc q e) c := by
  let a := edgeLabel e c.val.1
  let b := edgeLabel e c.val.2
  let x := ActiveArc.crossingPoint (cutArc q e) c
  have hab : a≠b := fun hh => (ne_of_lt c.property.1) (edgeLabel_injective e hh)
  have ha := (cut_edgeInterior_iff q e c.val.1 x).mp (ActiveArc.crossingPoint_mem _ c).1
  have hb := (cut_edgeInterior_iff q e c.val.2 x).mp (ActiveArc.crossingPoint_mem _ c).2
  rcases lt_or_gt_of_ne hab with hh|hh
  · let d : PolygonCrossing q := ⟨(a,b),hh,x,ha,hb⟩
    have hd : ¬Incident q e d := by
      rintro (hl|hr)
      · exact edgeLabel_ne_deleted e c.val.1 hl
      · exact edgeLabel_ne_deleted e c.val.2 hr
    exact ⟨⟨d,hd⟩,(DirectGLSSW.crossingPoint_eq_of_mem hq.size_ge_three q hq.g1 d x ha hb).symm⟩
  · let d : PolygonCrossing q := ⟨(b,a),hh,x,hb,ha⟩
    have hd : ¬Incident q e d := by
      rintro (hl|hr)
      · exact edgeLabel_ne_deleted e c.val.2 hl
      · exact edgeLabel_ne_deleted e c.val.1 hr
    exact ⟨⟨d,hd⟩,(DirectGLSSW.crossingPoint_eq_of_mem hq.size_ge_three q hq.g1 d x hb ha).symm⟩

def crossingToOriginal (c : ActiveArc.Crossing (cutArc q e)) : OffCrossing q e :=
  Classical.choose (exists_offCrossing_at q e hq c)

theorem crossingToOriginal_point (c : ActiveArc.Crossing (cutArc q e)) :
    DirectGLSSW.crossingPoint q (crossingToOriginal q e hq c).val=ActiveArc.crossingPoint (cutArc q e) c :=
  Classical.choose_spec (exists_offCrossing_at q e hq c)

include hq in
/-- Every original crossing away from the deleted edge is represented by physical cut edges. -/
theorem exists_cutCrossing_at (d : OffCrossing q e) :
    ∃ c : ActiveArc.Crossing (cutArc q e),
      ActiveArc.crossingPoint (cutArc q e) c=DirectGLSSW.crossingPoint q d.val := by
  have hl : d.val.val.1≠e := fun hh => d.property (Or.inl hh)
  have hr : d.val.val.2≠e := fun hh => d.property (Or.inr hh)
  obtain ⟨a,ha⟩ := exists_edgeLabel e d.val.val.1 hl
  obtain ⟨b,hb⟩ := exists_edgeLabel e d.val.val.2 hr
  have hab : a≠b := by
    intro hh
    apply crossing_edges_ne q d.val
    rw [← ha,← hb,hh]
  let x := DirectGLSSW.crossingPoint q d.val
  have hxa : ActiveArc.edgeInterior (cutArc q e) a x := by
    apply (cut_edgeInterior_iff q e a x).mpr
    rw [ha]
    exact crossingPoint_mem_left q d.val
  have hxb : ActiveArc.edgeInterior (cutArc q e) b x := by
    apply (cut_edgeInterior_iff q e b x).mpr
    rw [hb]
    exact crossingPoint_mem_right q d.val
  rcases lt_or_gt_of_ne hab with hh|hh
  · let c : ActiveArc.Crossing (cutArc q e) := ⟨(a,b),hh,x,hxa,hxb⟩
    exact ⟨c,crossingPoint_eq_of_mem_regular _ (cutArc_regular q e hq) c x hxa hxb⟩
  · let c : ActiveArc.Crossing (cutArc q e) := ⟨(b,a),hh,x,hxb,hxa⟩
    exact ⟨c,crossingPoint_eq_of_mem_regular _ (cutArc_regular q e hq) c x hxb hxa⟩

theorem crossingToOriginal_bijective : Function.Bijective (crossingToOriginal q e hq) := by
  constructor
  · intro c d hh
    apply ActiveArc.crossingPoint_injective _ (cutArc_regular q e hq).noTriple
    rw [← crossingToOriginal_point q e hq c,← crossingToOriginal_point q e hq d,hh]
  · intro d
    obtain ⟨c,hc⟩ := exists_cutCrossing_at q e hq d
    refine ⟨c,?_⟩
    apply Subtype.ext
    apply DirectGLSSW.crossingPoint_injective q hq.g2
    exact (crossingToOriginal_point q e hq c).trans hc

/-- Exact physical crossing-label equivalence; it excludes the deleted edge by construction. -/
def crossingEquiv : ActiveArc.Crossing (cutArc q e) ≃ OffCrossing q e :=
  Equiv.ofBijective (crossingToOriginal q e hq) (crossingToOriginal_bijective q e hq)

theorem crossingEquiv_point (c : ActiveArc.Crossing (cutArc q e)) :
    DirectGLSSW.crossingPoint q (crossingEquiv q e hq c).val=ActiveArc.crossingPoint (cutArc q e) c :=
  crossingToOriginal_point q e hq c

include hq in
/-- G2 identifies every physical branch through a represented crossing point. -/
theorem original_edge_at_crossing (c : PolygonCrossing q) (f : Fin (n+2))
    (hf : DirectGLSSW.edgeInterior q f (DirectGLSSW.crossingPoint q c)) :
    f=c.val.1 ∨ f=c.val.2 := by
  by_contra hh
  push_neg at hh
  exact hq.g2 c.val.1 c.val.2 f (DirectGLSSW.crossingPoint q c)
    (crossing_edges_ne q c) hh.2.symm hh.1.symm
    ⟨crossingPoint_mem_left q c,crossingPoint_mem_right q c,hf⟩

/-- The crossing correspondence preserves the actual incident edge, independent of
which increasing-label Boolean convention it acquires after rotation. -/
theorem crossingEquiv_visit_edge (c : ActiveArc.Crossing (cutArc q e)) (b : Bool) :
    edgeLabel e (ActiveArc.visitEdge (cutArc q e) (c,b))=(crossingEquiv q e hq c).val.val.1 ∨
    edgeLabel e (ActiveArc.visitEdge (cutArc q e) (c,b))=(crossingEquiv q e hq c).val.val.2 := by
  apply original_edge_at_crossing q hq (crossingEquiv q e hq c).val
  rw [crossingEquiv_point]
  apply (cut_edgeInterior_iff q e _ _).mp
  exact ⟨ActiveArc.visitParameter (cutArc q e) (c,b),ActiveArc.visitParameter_spec (cutArc q e) (c,b)⟩

/-- On the exposed chart every original crossing is physical in the cut arc. -/
def exposedCrossingEquiv (he : LeftExposed q e) :
    ActiveArc.Crossing (cutArc q e) ≃ PolygonCrossing q :=
  (crossingEquiv q e hq).trans
    { toFun := Subtype.val
      invFun := fun c => ⟨c,leftExposed_no_incident_crossing q hq e he c⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end DirectGLSSW.ActiveArc.ExposedChart
