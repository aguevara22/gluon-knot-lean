import PLArcSubdivisionData
import DirectGLSSW.AffineSegments

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace DirectGLSSW.HOMFLY.ArcSubdivision

variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ)

theorem old_vertex_ne_point (ht0 : 0<t) (ht1 : t<1) (v : Fin D.nVertex) :
    D.vertexPoint v ≠ point D e t :=
  D.vertices_avoid_arc_interiors v e t ht0 ht1

/-- The initial subarc uses the literal parameter interval (0,t). -/
theorem first_affine (s : ℝ) :
    affinePoint (D.vertexPoint (D.arcSource e)) (point D e t) s =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) (t*s) := by
  ext <;> simp only [point,affinePoint] <;> ring

/-- The terminal subarc uses the literal parameter interval (t,1). -/
theorem second_affine (s : ℝ) :
    affinePoint (point D e t) (D.vertexPoint (D.arcTarget e)) s =
      affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e))
        (t+(1-t)*s) := by
  ext <;> simp only [point,affinePoint] <;> ring

theorem first_parameter_bounds (ht0 : 0<t) (ht1 : t<1) (s : ℝ) (hs0 : 0<s) (hs1 : s<1) :
    0<t*s ∧ t*s<t ∧ t*s<1 := by
  have h:=mul_lt_of_lt_one_right ht0 hs1
  exact ⟨mul_pos ht0 hs0,h,h.trans ht1⟩

theorem second_parameter_bounds (ht0 : 0<t) (ht1 : t<1) (s : ℝ) (hs0 : 0<s) (hs1 : s<1) :
    0<t+(1-t)*s ∧ t<t+(1-t)*s ∧ t+(1-t)*s<1 := by
  have hp := mul_pos (sub_pos.mpr ht1) hs0
  have hl := mul_lt_of_lt_one_right (sub_pos.mpr ht1) hs1
  constructor
  · linarith
  constructor <;> linarith

private theorem endpoint_points_ne : D.vertexPoint (D.arcSource e) ≠ D.vertexPoint (D.arcTarget e) :=
  fun h => D.arc_endpoints_distinct e (D.vertexPoint_injective h)

theorem halves_interiors_disjoint (ht0 : 0<t) (ht1 : t<1)
    (s u : ℝ) (hs0 : 0<s) (hs1 : s<1) (hu0 : 0<u) (hu1 : u<1) :
    affinePoint (D.vertexPoint (D.arcSource e)) (point D e t) s ≠
      affinePoint (point D e t) (D.vertexPoint (D.arcTarget e)) u := by
  rw [first_affine,second_affine]
  intro h
  have he := affinePoint_injective _ _ (endpoint_points_ne D e) h
  have hs := first_parameter_bounds t ht0 ht1 s hs0 hs1
  have hu := second_parameter_bounds t ht0 ht1 u hu0 hu1
  linarith

theorem point_avoids_other_arc (ht0 : 0<t) (ht1 : t<1) (f : Fin D.nArc) (hef : e≠f)
    (s : ℝ) (hs0 : 0<s) (hs1 : s<1) :
    point D e t ≠ affinePoint (D.vertexPoint (D.arcSource f)) (D.vertexPoint (D.arcTarget f)) s :=
  D.arc_interiors_disjoint e f hef t s ht0 ht1 hs0 hs1

theorem first_tangent : point D e t-D.vertexPoint (D.arcSource e) =
    t • (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e)) := by
  ext <;> simp [point,affinePoint] <;> ring

theorem second_tangent : D.vertexPoint (D.arcTarget e)-point D e t =
    (1-t) • (D.vertexPoint (D.arcTarget e)-D.vertexPoint (D.arcSource e)) := by
  ext <;> simp [point,affinePoint] <;> ring
end DirectGLSSW.HOMFLY.ArcSubdivision
