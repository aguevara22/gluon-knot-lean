import HOMFLYTriangleSlice

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

theorem segment_horizontal_slice (a b : PlanarPoint ℝ)
    (ha : a.2 < 0) (hb : 0 < b.2) :
    segment ℝ a b ∩ {z : PlanarPoint ℝ | z.2 = 0} = {horizontalCut a b} := by
  have hd : b.2-a.2 ≠ 0 := by linarith
  ext z
  constructor
  · rintro ⟨⟨u,v,hu,hv,hs,hpoint⟩,hy⟩
    change z.2 = 0 at hy
    have hpy : u*a.2+v*b.2=0 := (congrArg Prod.snd hpoint).trans hy
    have hnum : v*(b.2-a.2) = -a.2 := by
      calc
        _ = (u*a.2+v*b.2)-a.2*(u+v) := by ring
        _ = -a.2 := by rw [hpy,hs]; ring
    have hve : v = -a.2/(b.2-a.2) := (eq_div_iff hd).2 hnum
    have hue : u = 1-v := by linarith
    apply Set.mem_singleton_iff.2
    rw [← hpoint]
    ext <;> dsimp [horizontalCut, affinePoint] <;> rw [hue,hve] <;> ring
  · intro hz
    have hz' := Set.mem_singleton_iff.1 hz
    subst z
    exact ⟨horizontalCut_mem_segment a b ha hb, horizontalCut_y a b ha hb⟩

theorem positive_segment_y (a b z : PlanarPoint ℝ) (ha : 0 < a.2) (hb : 0 < b.2)
    (hz : z ∈ segment ℝ a b) : 0 < z.2 := by
  rcases hz with ⟨u,v,hu,hv,hs,hz⟩
  have hy : u*a.2+v*b.2=z.2 := congrArg Prod.snd hz
  rcases lt_or_eq_of_le hu with hu | hu
  · have hp := mul_pos hu ha
    have hq := mul_nonneg hv (le_of_lt hb)
    linarith
  · have hv1 : v = 1 := by linarith
    rw [← hu,hv1] at hy
    have hy' : b.2 = z.2 := by simpa using hy
    exact hy' ▸ hb

theorem positive_segment_horizontal_slice (a b : PlanarPoint ℝ)
    (ha : 0 < a.2) (hb : 0 < b.2) :
    segment ℝ a b ∩ {z : PlanarPoint ℝ | z.2 = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.2
  rintro z ⟨hz,hy⟩
  have hp := positive_segment_y a b z ha hb hz
  change z.2 = 0 at hy
  linarith

theorem triangle_boundary_horizontal_slice (T : TrianglePatch)
    (ha : T.a.2 < 0) (hb : 0 < T.b.2) (hc : 0 < T.c.2) :
    T.boundary ∩ {z : PlanarPoint ℝ | z.2 = 0} =
      {horizontalCut T.a T.b, horizontalCut T.a T.c} := by
  unfold TrianglePatch.boundary
  rw [segment_symm ℝ T.c T.a]
  simp only [Set.union_inter_distrib_right, segment_horizontal_slice T.a T.b ha hb,
    segment_horizontal_slice T.a T.c ha hc, positive_segment_horizontal_slice T.b T.c hb hc]
  ext z
  simp only [Set.mem_union, Set.mem_empty_iff_false, or_false,
    Set.mem_singleton_iff, Set.mem_insert_iff]

theorem triangle_horizontal_cuts_ne (T : TrianglePatch)
    (ha : T.a.2 < 0) (hb : 0 < T.b.2) (hc : 0 < T.c.2) :
    horizontalCut T.a T.b ≠ horizontalCut T.a T.c := by
  intro heq
  obtain ⟨hb0,hb1⟩ := horizontalCut_parameter T.a T.b ha hb
  obtain ⟨hc0,hc1⟩ := horizontalCut_parameter T.a T.c ha hc
  apply onOpenSegment_common_origin_disjoint T.nondegenerate
    ⟨-T.a.2/(T.b.2-T.a.2),hb0,hb1,rfl⟩
  exact ⟨-T.a.2/(T.c.2-T.a.2),hc0,hc1,heq⟩

end
end DirectGLSSW.HOMFLY





