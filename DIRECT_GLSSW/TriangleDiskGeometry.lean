import ActualTriangleImage

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial

/-- The target triangle is the image of the standard nondegenerate triangular
 disk under this literal injective affine plane map. -/
theorem triangle_plane_injective (H : ℝ) :
    Function.Injective (fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),H+p.1/2+p.2)) := by
  intro p q h
  have hx := congrArg (fun x : ℂ × ℝ => x.1.re) h
  have hz := congrArg Prod.snd h
  dsimp at hx hz
  apply Prod.ext <;> dsimp <;> linarith

theorem triangle_plane_continuous (H : ℝ) :
    Continuous (fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),H+p.1/2+p.2)) := by
  fun_prop

/-- Complete boundary parametrizations of the affine standard triangle:
(0,1) to (1,0), then (1,0) to (0,0), then (0,0) to (0,1). -/
theorem triangle_plane_boundary (H : ℝ) (u : unitInterval) :
    (((u.val/4:ℝ):ℂ),H+u.val/2+(1-u.val)) =
      (((u.val/4:ℝ):ℂ),H+1-u.val/2) ∧
    ((((1-u.val)/4:ℝ):ℂ),H+(1-u.val)/2+0) =
      ((((1-u.val)/4:ℝ):ℂ),H+1/2-u.val/2) ∧
    (((0/4:ℝ):ℂ),H+0/2+u.val) = ((0:ℂ),H+u.val) := by
  constructor
  · apply Prod.ext <;> dsimp <;> ring
  constructor <;> apply Prod.ext <;> dsimp <;> simp <;> ring

/-- Every point of the filled standard triangle stays in the component slab. -/
theorem triangle_disk_height_bounds (H s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ 1) :
    H ≤ H+s/2+t ∧ H+s/2+t ≤ H+1 := by
  constructor <;> linarith

/-- Ordered component slabs separate the filled disks as well as their edges. -/
theorem triangle_disks_disjoint (H K : ℝ) (hHK : H+1 < K) :
    Disjoint
      ((fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),H+p.1/2+p.2)) ''
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1})
      ((fun p : ℝ × ℝ => (((p.1/4:ℝ):ℂ),K+p.1/2+p.2)) ''
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1}) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,hp,rfl⟩ ⟨q,hq,heq⟩
  have hb := triangle_disk_height_bounds H p.1 p.2 hp.1 hp.2.1 hp.2.2
  have hc := triangle_disk_height_bounds K q.1 q.2 hq.1 hq.2.1 hq.2.2
  have hz := congrArg Prod.snd heq
  dsimp at hz
  linarith

end DirectGLSSW.DescendingSpatial





