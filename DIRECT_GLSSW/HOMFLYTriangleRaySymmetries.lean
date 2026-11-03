import HOMFLYDiskAttachmentBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
attribute [local instance] Classical.propDecidable

def reflectY : PlanarPoint ℝ →ₗ[ℝ] PlanarPoint ℝ where
  toFun z := (z.1,-z.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' r z := by ext <;> simp

@[simp] theorem reflectY_apply (z : PlanarPoint ℝ) : reflectY z = (z.1,-z.2) := rfl
@[simp] theorem reflectY_twice (z : PlanarPoint ℝ) : reflectY (reflectY z) = z := by
  ext <;> simp

theorem reflectY_fixed_axis (z : PlanarPoint ℝ) (hz : z.2=0) : reflectY z=z := by
  ext <;> simp [hz]

theorem reflectY_image_mem_fixed (S : Set (PlanarPoint ℝ)) (z : PlanarPoint ℝ)
    (hz : z.2=0) : z ∈ reflectY '' S ↔ z ∈ S := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hwz : w=z := by
      calc
        w = reflectY (reflectY w) := (reflectY_twice w).symm
        _ = reflectY z := congrArg reflectY he
        _ = z := reflectY_fixed_axis z hz
    exact hwz ▸ hw
  · intro h
    exact ⟨z,h,reflectY_fixed_axis z hz⟩

namespace TrianglePatch

def rotate (T : TrianglePatch) : TrianglePatch where
  a := T.b
  b := T.c
  c := T.a
  nondegenerate := by
    have he : planarDet (T.c-T.b) (T.a-T.b) = planarDet (T.b-T.a) (T.c-T.a) := by
      dsimp [planarDet]; ring
    rw [he]
    exact T.nondegenerate

@[simp] theorem rotate_fill (T : TrianglePatch) : T.rotate.fill = T.fill := by
  unfold fill rotate
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

@[simp] theorem rotate_boundary (T : TrianglePatch) : T.rotate.boundary = T.boundary := by
  ext z
  simp only [boundary, rotate, Set.mem_union]
  tauto

def reflected (T : TrianglePatch) : TrianglePatch where
  a := reflectY T.a
  b := reflectY T.b
  c := reflectY T.c
  nondegenerate := by
    have he : planarDet (reflectY T.b-reflectY T.a) (reflectY T.c-reflectY T.a) =
        -planarDet (T.b-T.a) (T.c-T.a) := by
      dsimp [planarDet,reflectY]; ring
    rw [he]
    exact neg_ne_zero.mpr T.nondegenerate

theorem reflected_fill_image (T : TrianglePatch) : T.reflected.fill = reflectY '' T.fill := by
  change convexHull ℝ {T.reflected.a,T.reflected.b,T.reflected.c} =
    reflectY '' convexHull ℝ {T.a,T.b,T.c}
  rw [reflectY.image_convexHull]
  simp only [reflected, Set.image_insert_eq, Set.image_singleton]

theorem reflected_boundary_image (T : TrianglePatch) :
    T.reflected.boundary = reflectY '' T.boundary := by
  have hab : reflectY '' segment ℝ T.a T.b = segment ℝ (reflectY T.a) (reflectY T.b) :=
    image_segment ℝ reflectY.toAffineMap T.a T.b
  have hbc : reflectY '' segment ℝ T.b T.c = segment ℝ (reflectY T.b) (reflectY T.c) :=
    image_segment ℝ reflectY.toAffineMap T.b T.c
  have hca : reflectY '' segment ℝ T.c T.a = segment ℝ (reflectY T.c) (reflectY T.a) :=
    image_segment ℝ reflectY.toAffineMap T.c T.a
  simp only [boundary, reflected, Set.image_union, hab, hbc, hca]

theorem reflected_boundary_axis_mem (T : TrianglePatch) (z : PlanarPoint ℝ) (hz : z.2=0) :
    z ∈ T.reflected.boundary ↔ z ∈ T.boundary := by
  rw [reflected_boundary_image]
  exact reflectY_image_mem_fixed T.boundary z hz

theorem reflected_fill_origin (T : TrianglePatch) :
    (0 : PlanarPoint ℝ) ∈ T.reflected.fill ↔ (0 : PlanarPoint ℝ) ∈ T.fill := by
  rw [reflected_fill_image]
  exact reflectY_image_mem_fixed T.fill 0 rfl

theorem reflected_boundary_ray (T : TrianglePatch) :
    T.reflected.boundary ∩ positiveHorizontalRay = T.boundary ∩ positiveHorizontalRay := by
  ext z
  by_cases hz : z ∈ positiveHorizontalRay
  · simp only [Set.mem_inter_iff, hz, and_true]
    exact T.reflected_boundary_axis_mem z hz.1
  · simp only [Set.mem_inter_iff,hz,and_false]

end TrianglePatch

/-- A parity assertion for the actual triangle, with boundary points excluded. -/
def TriangleRayParity (T : TrianglePatch) : Prop :=
  (0 : PlanarPoint ℝ) ∉ T.boundary →
  (T.boundary ∩ positiveHorizontalRay).ncard % 2 =
    if (0 : PlanarPoint ℝ) ∈ T.fill then 1 else 0

theorem triangleRayParity_rotate (T : TrianglePatch) : TriangleRayParity T.rotate ↔ TriangleRayParity T := by
  simp only [TriangleRayParity,TrianglePatch.rotate_boundary,TrianglePatch.rotate_fill]

theorem triangleRayParity_reflected (T : TrianglePatch) :
    TriangleRayParity T.reflected ↔ TriangleRayParity T := by
  simp only [TriangleRayParity,T.reflected_boundary_ray,T.reflected_fill_origin,
    T.reflected_boundary_axis_mem 0 rfl]

theorem triangleRayParity_all_positive (T : TrianglePatch)
    (ha : 0<T.a.2) (hb : 0<T.b.2) (hc : 0<T.c.2) : TriangleRayParity T := by
  have hfill : T.fill ⊆ {z : PlanarPoint ℝ | 0<z.2} := by
    apply convexHull_min
    · intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl|rfl|rfl <;> assumption
    · intro x hx y hy u v hu hv hs
      exact positive_segment_y x y (u • x+v • y) hx hy ⟨u,v,hu,hv,hs,rfl⟩
  have hzero : (0 : PlanarPoint ℝ) ∉ T.fill := by
    intro h
    have hh := hfill h
    change (0:ℝ)<0 at hh
    exact (lt_irrefl 0) hh
  have hempty : T.boundary ∩ positiveHorizontalRay = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.2
    rintro z ⟨hz,hR⟩
    have hy : 0<z.2 := hfill (T.boundary_subset_fill hz)
    rw [hR.1] at hy
    exact (lt_irrefl 0) hy
  intro _
  simp [hempty,hzero]

end
end DirectGLSSW.HOMFLY




