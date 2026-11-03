import HOMFLYTriangleRayParity

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

 theorem noncollinear_segment_intersection (a b c z : PlanarPoint ℝ)
    (hdet : planarDet (b-a) (c-a) ≠ 0)
    (hab : z ∈ segment ℝ a b) (hac : z ∈ segment ℝ a c) : z = a := by
  rcases hab with ⟨u,v,hu,hv,hs,hz⟩
  have hab' : z-a = v • (b-a) := by
    rw [← hz]
    have hue : u = 1-v := by linarith
    rw [hue]
    ext <;> dsimp <;> ring
  rcases hac with ⟨s,t,hs0,ht,hst,hz'⟩
  have hac' : z-a = t • (c-a) := by
    rw [← hz']
    have hse : s = 1-t := by linarith
    rw [hse]
    ext <;> dsimp <;> ring
  have hvd : v * planarDet (b-a) (c-a) = 0 := by
    calc
      _ = planarDet (z-a) (c-a) := by rw [hab']; dsimp [planarDet]; ring
      _ = 0 := by rw [hac']; dsimp [planarDet]; ring
  have hv0 := (mul_eq_zero.mp hvd).resolve_right hdet
  rw [hv0, zero_smul] at hab'
  exact sub_eq_zero.mp hab'

namespace TrianglePatch

theorem boundary_subset_fill (T : TrianglePatch) : T.boundary ⊆ T.fill := by
  have ha : T.a ∈ T.fill := subset_convexHull ℝ _ (by simp)
  have hb : T.b ∈ T.fill := subset_convexHull ℝ _ (by simp)
  have hc : T.c ∈ T.fill := subset_convexHull ℝ _ (by simp)
  exact Set.union_subset (Set.union_subset
    ((convex_convexHull ℝ _).segment_subset ha hb)
    ((convex_convexHull ℝ _).segment_subset hb hc))
    ((convex_convexHull ℝ _).segment_subset hc ha)

theorem edge_other_sides_disjoint_away_endpoints (T : TrianglePatch) (z : PlanarPoint ℝ)
    (hza : z ≠ T.a) (hzb : z ≠ T.b)
    (hedge : z ∈ segment ℝ T.a T.b) :
    z ∉ segment ℝ T.b T.c ∪ segment ℝ T.c T.a := by
  rintro (hbc | hca)
  · have hd : planarDet (T.a-T.b) (T.c-T.b) ≠ 0 := by
      have he : planarDet (T.a-T.b) (T.c-T.b) = -planarDet (T.b-T.a) (T.c-T.a) := by
        dsimp [planarDet]; ring
      rw [he]
      exact neg_ne_zero.mpr T.nondegenerate
    apply hzb
    apply noncollinear_segment_intersection T.b T.a T.c z hd
    · simpa only [segment_symm ℝ T.b T.a] using hedge
    · exact hbc
  · apply hza
    apply noncollinear_segment_intersection T.a T.b T.c z T.nondegenerate hedge
    simpa only [segment_symm ℝ T.a T.c] using hca

end TrianglePatch

namespace FiniteDiskCertificate

theorem boundary_subset_region {K B : Set (PlanarPoint ℝ)} (W : FiniteDiskCertificate K B) :
    B ⊆ K := by
  induction W with
  | triangle T => exact T.boundary_subset_fill
  | attach previous T boundary_edge exact_intersection ih =>
      intro z hz
      rcases hz with (h | h) | h
      · exact Or.inl (ih h.1)
      · exact Or.inr (T.boundary_subset_fill (Or.inl (Or.inr h)))
      · exact Or.inr (T.boundary_subset_fill (Or.inr h))

/-- At a point away from the attachment endpoints, the common boundary edge
cancels. This is the geometric input for finite generic-ray parity induction. -/
theorem attach_boundary_xor {K B : Set (PlanarPoint ℝ)}
    (W : FiniteDiskCertificate K B) (T : TrianglePatch)
    (boundary_edge : segment ℝ T.a T.b ⊆ B)
    (exact_intersection : K ∩ T.fill = segment ℝ T.a T.b)
    (z : PlanarPoint ℝ) (hza : z ≠ T.a) (hzb : z ≠ T.b) :
    z ∈ ((B \ openSegment ℝ T.a T.b) ∪ segment ℝ T.b T.c ∪ segment ℝ T.c T.a) ↔
      ((z ∈ B ∧ z ∉ T.boundary) ∨ (z ∉ B ∧ z ∈ T.boundary)) := by
  have hopen : z ∈ openSegment ℝ T.a T.b ↔ z ∈ segment ℝ T.a T.b := by
    constructor
    · intro hz; exact openSegment_subset_segment ℝ T.a T.b hz
    · exact mem_openSegment_of_ne_left_right hza.symm hzb.symm
  have hedge : z ∈ segment ℝ T.a T.b → z ∈ B := fun hz => boundary_edge hz
  have hdis : ¬(z ∈ B ∧ z ∈ segment ℝ T.b T.c ∪ segment ℝ T.c T.a) := by
    rintro ⟨hzB,hzF⟩
    have hzT : z ∈ T.boundary := by rcases hzF with h|h; exact Or.inl (Or.inr h); exact Or.inr h
    have hzE : z ∈ segment ℝ T.a T.b := by
      rw [← exact_intersection]
      exact ⟨W.boundary_subset_region hzB,T.boundary_subset_fill hzT⟩
    exact T.edge_other_sides_disjoint_away_endpoints z hza hzb hzE hzF
  simp only [TrianglePatch.boundary, Set.mem_union, Set.mem_diff, hopen]
  simp only [Set.mem_union] at hdis
  tauto

end FiniteDiskCertificate
end
end DirectGLSSW.HOMFLY




