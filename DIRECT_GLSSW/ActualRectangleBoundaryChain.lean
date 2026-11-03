import ActualRectangleSidePairing
import RetainedRectangleAngles

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

def rectangleSideIncrement {D : PLLinkDiagram} {T : BasedTraversal D} {C : diagramComponent D}
    (e : RetainedRectangleSide T C) : ℝ :=
  Complex.arg (basedUniformSecant T C (rectangleSideFinish e).1 (rectangleSideFinish e).2 /
    basedUniformSecant T C (rectangleSideStart e).1 (rectangleSideStart e).2)

def parameterInRectangle {D : PLLinkDiagram} {T : BasedTraversal D} {C : diagramComponent D}
    (r : RetainedRectangleIndex T C) (p : ℝ × ℝ) : Prop :=
  p.1 ∈ Set.Icc r.val.1.1 r.val.1.2 ∧ p.2 ∈ Set.Icc r.val.2.1 r.val.2.2

theorem rectangleSide_points_in_rectangle {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) :
    parameterInRectangle e.1 (rectangleSideStart e) ∧
      parameterInRectangle e.1 (rectangleSideFinish e) := by
  have hc := retainedRectangle_axis_cells e.1
  rcases e with ⟨r,k⟩
  fin_cases k <;> simp [parameterInRectangle,rectangleSideStart,rectangleSideFinish,
    Set.mem_Icc,hc.1.2.2.1.le,hc.2.2.2.1.le]

theorem rectangleSide_avoids_zero {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) :
    (0 : ℂ) ∉ segment ℝ
      (basedUniformSecant T C (rectangleSideStart e).1 (rectangleSideStart e).2)
      (basedUniformSecant T C (rectangleSideFinish e).1 (rectangleSideFinish e).2) := by
  have hp := rectangleSide_points_in_rectangle e
  intro hz
  exact (retainedSecantTriangle_origin_excluded T C _ _ _ _ _ _ _ _ _ _ e.1.property
    hp.1.1 hp.2.1 hp.1.1 hp.1.2 hp.2.2 hp.1.2)
    (origin_triangle_of_segment _ _ _ hz)

theorem rectangleSideIncrement_reverse {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C)
    (hne : rectangleSideReverse e ≠ e) :
    rectangleSideIncrement (rectangleSideReverse e) = -rectangleSideIncrement e := by
  have hr := rectangleSideReverse_nonfixed_endpoints e hne
  unfold rectangleSideIncrement
  rw [hr.1,hr.2]
  exact segment_arg_reverse _ _ (rectangleSide_avoids_zero e)

theorem actualRectangle_nonfixed_sides_cancel {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    ∑ e ∈ (Finset.univ.filter (fun e : RetainedRectangleSide T C => rectangleSideReverse e ≠ e)),
      rectangleSideIncrement e = 0 := by
  classical
  let S : Finset (RetainedRectangleSide T C) := Finset.univ.filter (fun e => rectangleSideReverse e ≠ e)
  change ∑ e ∈ S, rectangleSideIncrement e = 0
  refine Finset.sum_involution (s := S) (f := rectangleSideIncrement)
    (g := fun e _ => rectangleSideReverse e) ?_ ?_ ?_ ?_
  · intro e he
    have hn : rectangleSideReverse e ≠ e := by simpa [S] using he
    rw [rectangleSideIncrement_reverse e hn]
    exact add_neg_cancel _
  · intro e he _
    exact (show rectangleSideReverse e ≠ e by simpa [S] using he)
  · intro e he
    have hn : rectangleSideReverse e ≠ e := by simpa [S] using he
    change rectangleSideReverse e ∈ S
    simpa [S,rectangleSideReverse_involutive e] using Ne.symm hn
  · intro e he
    exact rectangleSideReverse_involutive e

theorem actualRectangle_total_sides_zero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    ∑ e : RetainedRectangleSide T C, rectangleSideIncrement e = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro r hr
  simpa [Fin.sum_univ_four,rectangleSideIncrement,rectangleSideStart,rectangleSideFinish] using
    retainedSecantRectangle_angle_zero T C r.val.1.1 r.val.1.2 r.val.2.1 r.val.2.2 r.property

/-- SOURCE-PREPARED, UNCOMPILED: a single actual finite-chain consumer.
Every incidence/avoidance datum is derived from actual D/T/C and retained
cells. The residual fixed sides still need geometric boundary classification. -/
theorem actualRetainedRectangle_boundary_balance {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) :
    ∑ e ∈ (Finset.univ.filter (fun e : RetainedRectangleSide T C => rectangleSideReverse e = e)),
      rectangleSideIncrement e = 0 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (RetainedRectangleSide T C)) (fun e => rectangleSideReverse e = e)
    rectangleSideIncrement
  rw [actualRectangle_nonfixed_sides_cancel T C,add_zero] at hsplit
  exact hsplit.trans (actualRectangle_total_sides_zero T C)

end
end DirectGLSSW.HOMFLY.PrincipalTurning




