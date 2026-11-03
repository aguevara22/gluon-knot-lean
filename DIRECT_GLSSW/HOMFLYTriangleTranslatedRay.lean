import HOMFLYTriangleGenericRay

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
attribute [local instance] Classical.propDecidable

def recenter (q : PlanarPoint ℝ) : PlanarPoint ℝ ≃ᵃ[ℝ] PlanarPoint ℝ :=
  AffineEquiv.constVAdd ℝ (PlanarPoint ℝ) (-q)

@[simp] theorem recenter_apply (q z : PlanarPoint ℝ) : recenter q z = z-q := by
  change -q+z=z-q
  abel

@[simp] theorem recenter_self (q : PlanarPoint ℝ) : recenter q q=0 := by simp

theorem recenter_image_origin (q : PlanarPoint ℝ) (S : Set (PlanarPoint ℝ)) :
    (0 : PlanarPoint ℝ) ∈ recenter q '' S ↔ q ∈ S := by
  constructor
  · rintro ⟨z,hz,he⟩
    have h : z=q := (recenter q).injective (he.trans (recenter_self q).symm)
    exact h ▸ hz
  · intro h
    exact ⟨q,h,recenter_self q⟩

def horizontalRayFrom (q : PlanarPoint ℝ) : Set (PlanarPoint ℝ) :=
  {z | z.2=q.2 ∧ q.1<z.1}

theorem recenter_ray_mem (q z : PlanarPoint ℝ) :
    recenter q z ∈ positiveHorizontalRay ↔ z ∈ horizontalRayFrom q := by
  simp only [positiveHorizontalRay,horizontalRayFrom,Set.mem_setOf_eq,recenter_apply,Prod.snd_sub,Prod.fst_sub]
  exact and_congr sub_eq_zero (sub_pos)

namespace TrianglePatch

def recentered (T : TrianglePatch) (q : PlanarPoint ℝ) : TrianglePatch where
  a := recenter q T.a
  b := recenter q T.b
  c := recenter q T.c
  nondegenerate := by
    simpa only [recenter_apply,sub_sub_sub_cancel_right] using T.nondegenerate

theorem recentered_fill_image (T : TrianglePatch) (q : PlanarPoint ℝ) :
    (T.recentered q).fill = recenter q '' T.fill := by
  have he := (recenter q).toAffineMap.image_convexHull ({T.a,T.b,T.c} : Set (PlanarPoint ℝ))
  simpa only [recentered,fill,Set.image_insert_eq,Set.image_singleton] using he.symm

theorem recentered_boundary_image (T : TrianglePatch) (q : PlanarPoint ℝ) :
    (T.recentered q).boundary = recenter q '' T.boundary := by
  have hab : recenter q '' segment ℝ T.a T.b = segment ℝ (recenter q T.a) (recenter q T.b) :=
    image_segment ℝ (recenter q).toAffineMap T.a T.b
  have hbc : recenter q '' segment ℝ T.b T.c = segment ℝ (recenter q T.b) (recenter q T.c) :=
    image_segment ℝ (recenter q).toAffineMap T.b T.c
  have hca : recenter q '' segment ℝ T.c T.a = segment ℝ (recenter q T.c) (recenter q T.a) :=
    image_segment ℝ (recenter q).toAffineMap T.c T.a
  simp only [boundary,recentered,Set.image_union,hab,hbc,hca]

theorem recentered_boundary_ray_image (T : TrianglePatch) (q : PlanarPoint ℝ) :
    (T.recentered q).boundary ∩ positiveHorizontalRay =
      recenter q '' (T.boundary ∩ horizontalRayFrom q) := by
  rw [recentered_boundary_image]
  ext z
  constructor
  · rintro ⟨⟨w,hw,rfl⟩,hR⟩
    exact ⟨w,⟨hw,(recenter_ray_mem q w).mp hR⟩,rfl⟩
  · rintro ⟨w,⟨hw,hR⟩,rfl⟩
    exact ⟨⟨w,hw,rfl⟩,(recenter_ray_mem q w).mpr hR⟩

end TrianglePatch

theorem triangle_translated_ray_parity (T : TrianglePatch) (q : PlanarPoint ℝ)
    (ha : T.a.2 ≠ q.2) (hb : T.b.2 ≠ q.2) (hc : T.c.2 ≠ q.2)
    (hq : q ∉ T.boundary) :
    (T.boundary ∩ horizontalRayFrom q).Finite ∧
    (T.boundary ∩ horizontalRayFrom q).ncard % 2 =
      if q ∈ T.fill then 1 else 0 := by
  have ha' : (T.recentered q).a.2 ≠ 0 := by
    change (recenter q T.a).2 ≠ 0
    simpa only [recenter_apply,Prod.snd_sub,sub_ne_zero] using ha
  have hb' : (T.recentered q).b.2 ≠ 0 := by
    change (recenter q T.b).2 ≠ 0
    simpa only [recenter_apply,Prod.snd_sub,sub_ne_zero] using hb
  have hc' : (T.recentered q).c.2 ≠ 0 := by
    change (recenter q T.c).2 ≠ 0
    simpa only [recenter_apply,Prod.snd_sub,sub_ne_zero] using hc
  have hzero : (0 : PlanarPoint ℝ) ∉ (T.recentered q).boundary := by
    rw [T.recentered_boundary_image q,recenter_image_origin]
    exact hq
  have hf := triangle_positive_ray_finite (T.recentered q) ha' hb' hc'
  have hp := triangle_positive_ray_parity_generic (T.recentered q) ha' hb' hc' hzero
  rw [T.recentered_boundary_ray_image q] at hf hp
  constructor
  · exact hf.of_finite_image (recenter q).injective.injOn
  · rw [Set.ncard_image_of_injective _ (recenter q).injective,
      T.recentered_fill_image q,recenter_image_origin] at hp
    exact hp

end
end DirectGLSSW.HOMFLY


