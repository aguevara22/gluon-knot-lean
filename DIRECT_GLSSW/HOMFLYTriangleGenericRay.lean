import HOMFLYTriangleRaySymmetries

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem triangleRayParity_positive_a (T : TrianglePatch)
    (ha : 0<T.a.2) (hb : T.b.2 ≠ 0) (hc : T.c.2 ≠ 0) : TriangleRayParity T := by
  rcases lt_or_gt_of_ne hb with hb | hb <;> rcases lt_or_gt_of_ne hc with hc | hc
  · apply (triangleRayParity_reflected T).mp
    exact triangle_positive_ray_parity T.reflected (by change -T.a.2<0; linarith)
      (by change 0 < -T.b.2; linarith) (by change 0 < -T.c.2; linarith)
  · apply (triangleRayParity_rotate T).mp
    exact triangle_positive_ray_parity T.rotate hb hc ha
  · apply (triangleRayParity_rotate T).mp
    apply (triangleRayParity_rotate T.rotate).mp
    exact triangle_positive_ray_parity T.rotate.rotate hc ha hb
  · exact triangleRayParity_all_positive T ha hb hc

theorem triangleRayParity_of_vertices_off_axis (T : TrianglePatch)
    (ha : T.a.2 ≠ 0) (hb : T.b.2 ≠ 0) (hc : T.c.2 ≠ 0) : TriangleRayParity T := by
  rcases lt_or_gt_of_ne ha with han | hap
  · rcases lt_or_gt_of_ne hb with hbn | hbp
    · rcases lt_or_gt_of_ne hc with hcn | hcp
      · apply (triangleRayParity_reflected T).mp
        exact triangleRayParity_all_positive T.reflected
          (by change 0 < -T.a.2; linarith)
          (by change 0 < -T.b.2; linarith)
          (by change 0 < -T.c.2; linarith)
      · apply (triangleRayParity_rotate T).mp
        apply (triangleRayParity_rotate T.rotate).mp
        exact triangleRayParity_positive_a T.rotate.rotate hcp ha hb
    · apply (triangleRayParity_rotate T).mp
      exact triangleRayParity_positive_a T.rotate hbp hc ha
  · exact triangleRayParity_positive_a T hap hb hc

/-- Every nondegenerate real triangle has the correct generic horizontal ray
crossing parity; the statement uses its actual convex hull and boundary sets. -/
theorem triangle_positive_ray_parity_generic (T : TrianglePatch)
    (ha : T.a.2 ≠ 0) (hb : T.b.2 ≠ 0) (hc : T.c.2 ≠ 0)
    (horigin : (0 : PlanarPoint ℝ) ∉ T.boundary) :
    (T.boundary ∩ positiveHorizontalRay).ncard % 2 =
      if (0 : PlanarPoint ℝ) ∈ T.fill then 1 else 0 :=
  triangleRayParity_of_vertices_off_axis T ha hb hc horigin

theorem segment_axis_intersection_finite (a b : PlanarPoint ℝ) (ha : a.2 ≠ 0) :
    (segment ℝ a b ∩ {z : PlanarPoint ℝ | z.2=0}).Finite := by
  by_cases hab : a.2=b.2
  · have he : segment ℝ a b ∩ {z : PlanarPoint ℝ | z.2=0} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.2
      rintro z ⟨⟨u,v,hu,hv,hs,hz⟩,hy⟩
      have hp : u*a.2+v*b.2=z.2 := congrArg Prod.snd hz
      change z.2=0 at hy
      rw [← hab,← add_mul,hs,one_mul,hy] at hp
      exact ha hp
    rw [he]
    exact Set.finite_empty
  · apply (Set.finite_singleton (horizontalCut a b)).subset
    rintro z ⟨⟨u,v,hu,hv,hs,hz⟩,hy⟩
    change z.2=0 at hy
    have hd : b.2-a.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hp : u*a.2+v*b.2=0 := (congrArg Prod.snd hz).trans hy
    have hnum : v*(b.2-a.2) = -a.2 := by
      calc
        _ = (u*a.2+v*b.2)-a.2*(u+v) := by ring
        _ = -a.2 := by rw [hp,hs]; ring
    have hv' : v = -a.2/(b.2-a.2) := (eq_div_iff hd).2 hnum
    have hu' : u=1-v := by linarith
    apply Set.mem_singleton_iff.2
    rw [← hz]
    ext <;> dsimp [horizontalCut,affinePoint] <;> rw [hu',hv'] <;> ring

theorem triangle_positive_ray_finite (T : TrianglePatch)
    (ha : T.a.2 ≠ 0) (hb : T.b.2 ≠ 0) (hc : T.c.2 ≠ 0) :
    (T.boundary ∩ positiveHorizontalRay).Finite := by
  have haxis : (T.boundary ∩ {z : PlanarPoint ℝ | z.2=0}).Finite := by
    simp only [TrianglePatch.boundary, Set.union_inter_distrib_right]
    exact ((segment_axis_intersection_finite T.a T.b ha).union
      (segment_axis_intersection_finite T.b T.c hb)).union
      (segment_axis_intersection_finite T.c T.a hc)
  apply haxis.subset
  rintro z ⟨hz,hR⟩
  exact ⟨hz,hR.1⟩

end
end DirectGLSSW.HOMFLY



