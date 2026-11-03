import HOMFLYDiskAttachmentBoundary

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem difference_union_ncard_parity {α : Type*} (S T : Set α)
    (hS : S.Finite) (hT : T.Finite) :
    ((S \ T) ∪ (T \ S)).ncard % 2 = (S.ncard + T.ncard) % 2 := by
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Set.disjoint_left.2
    intro x hx hy
    exact hx.2 hy.1
  rw [Set.ncard_union_eq hd hS.diff hT.diff]
  have h1 := Set.ncard_diff_add_ncard S T hS hT
  have h2 := Set.ncard_diff_add_ncard T S hT hS
  rw [Set.union_comm T S] at h2
  omega

namespace FiniteDiskCertificate

/-- Actual boundary crossing counts add modulo two under a checked triangle
attachment. The test set can be any generic ray with finite intersections. -/
theorem attach_boundary_ncard_parity {K B : Set (PlanarPoint ℝ)}
    (W : FiniteDiskCertificate K B) (T : TrianglePatch)
    (boundary_edge : segment ℝ T.a T.b ⊆ B)
    (exact_intersection : K ∩ T.fill = segment ℝ T.a T.b)
    (R : Set (PlanarPoint ℝ)) (ha : T.a ∉ R) (hb : T.b ∉ R)
    (hB : (B ∩ R).Finite) (hT : (T.boundary ∩ R).Finite) :
    (((B \ openSegment ℝ T.a T.b) ∪ segment ℝ T.b T.c ∪ segment ℝ T.c T.a) ∩ R).ncard % 2 =
      ((B ∩ R).ncard + (T.boundary ∩ R).ncard) % 2 := by
  have he : ((B \ openSegment ℝ T.a T.b) ∪ segment ℝ T.b T.c ∪ segment ℝ T.c T.a) ∩ R =
      ((B ∩ R) \ (T.boundary ∩ R)) ∪ ((T.boundary ∩ R) \ (B ∩ R)) := by
    ext z
    by_cases hzR : z ∈ R
    · have hza : z ≠ T.a := by intro h; exact ha (h ▸ hzR)
      have hzb : z ≠ T.b := by intro h; exact hb (h ▸ hzR)
      rw [Set.mem_inter_iff, W.attach_boundary_xor T boundary_edge exact_intersection z hza hzb]
      simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff, hzR, and_true]
      tauto
    · simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff, hzR, and_false,
        not_false_eq_true, false_and, or_self]
  rw [he]
  exact difference_union_ncard_parity (B ∩ R) (T.boundary ∩ R) hB hT

/-- Off the gluing edge, the actual region membership indicators add modulo two. -/
theorem attach_region_indicator {K B : Set (PlanarPoint ℝ)}
    (_W : FiniteDiskCertificate K B) (T : TrianglePatch)
    (exact_intersection : K ∩ T.fill = segment ℝ T.a T.b)
    (z : PlanarPoint ℝ) (hz : z ∉ segment ℝ T.a T.b) :
    (if z ∈ K ∪ T.fill then (1 : ℕ) else 0) =
      ((if z ∈ K then 1 else 0) + (if z ∈ T.fill then 1 else 0)) % 2 := by
  have hdis : ¬ (z ∈ K ∧ z ∈ T.fill) := by
    intro h
    apply hz
    rw [← exact_intersection]
    exact h
  by_cases hK : z ∈ K <;> by_cases hT : z ∈ T.fill <;>
    simp_all only [Set.mem_union, or_self, or_true, or_false, true_or, false_or,
      ite_true, ite_false, and_self, not_true_eq_false, Nat.reduceAdd, Nat.reduceMod]

end FiniteDiskCertificate
end
end DirectGLSSW.HOMFLY



