import PLArcSubdivisionEmbedding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ)

private theorem point_ne_parameter (u : ℝ) (hu : u≠t) :
    point D e t ≠ affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) u := by
  intro h
  have hn : D.vertexPoint (D.arcSource e) ≠ D.vertexPoint (D.arcTarget e) :=
    fun he => D.arc_endpoints_distinct e (D.vertexPoint_injective he)
  have he := affinePoint_injective _ _ hn h
  exact hu he.symm

theorem vertices_avoid_arc_interiors (ht0 : 0<t) (ht1 : t<1) :
    ∀ v : Fin (D.nVertex+1), ∀ a : Fin (D.nArc+1), ∀ s : ℝ,
      0<s → s<1 → vertexPoint D e t v ≠ arcPoint D e t a s := by
  intro v
  refine Fin.lastCases ?_ (fun v=>?_) v
  · intro a
    refine Fin.lastCases ?_ (fun a=>?_) a
    · intro s hs0 hs1
      rw [vertexPoint_new,arcPoint_new]
      exact point_ne_parameter D e t _ (ne_of_gt (second_parameter_bounds t ht0 ht1 s hs0 hs1).2.1)
    · intro s hs0 hs1
      rw [vertexPoint_new,arcPoint_old]
      by_cases ha : a=e
      · rw [if_pos ha]
        exact point_ne_parameter D e t _ (ne_of_lt (first_parameter_bounds t ht0 ht1 s hs0 hs1).2.1)
      · rw [if_neg ha]
        exact point_avoids_other_arc D e t ht0 ht1 a (Ne.symm ha) s hs0 hs1
  · intro a
    refine Fin.lastCases ?_ (fun a=>?_) a
    · intro s hs0 hs1
      rw [vertexPoint_old,arcPoint_new]
      have hb:=second_parameter_bounds t ht0 ht1 s hs0 hs1
      exact D.vertices_avoid_arc_interiors v e _ hb.1 hb.2.2
    · intro s hs0 hs1
      rw [vertexPoint_old,arcPoint_old]
      by_cases ha : a=e
      · rw [if_pos ha]
        have hb:=first_parameter_bounds t ht0 ht1 s hs0 hs1
        exact D.vertices_avoid_arc_interiors v e _ hb.1 hb.2.2
      · rw [if_neg ha]
        exact D.vertices_avoid_arc_interiors v a s hs0 hs1
end DirectGLSSW.HOMFLY.ArcSubdivision
