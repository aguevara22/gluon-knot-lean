import HOMFLYTriangleBoundarySlice
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem weighted_positive (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u+v=1) : 0 < u*a+v*b := by
  have hmin : 0 < min a b := lt_min ha hb
  have hlo := add_le_add (mul_le_mul_of_nonneg_left (min_le_left a b) hu)
    (mul_le_mul_of_nonneg_left (min_le_right a b) hv)
  rw [← add_mul, hs, one_mul] at hlo
  exact lt_of_lt_of_le hmin hlo

theorem origin_mem_axis_segment_of_opposite (p q : PlanarPoint ℝ)
    (hpy : p.2 = 0) (hqy : q.2 = 0) (hp : p.1 < 0) (hq : 0 < q.1) :
    (0 : PlanarPoint ℝ) ∈ segment ℝ p q := by
  have hd : 0 < q.1-p.1 := by linarith
  let t := -p.1/(q.1-p.1)
  have ht0 : 0 < t := div_pos (by linarith) hd
  have ht1 : t < 1 := (div_lt_one hd).2 (by linarith)
  refine ⟨1-t,t,by linarith,le_of_lt ht0,by ring,?_⟩
  ext
  · change (1-t)*p.1+t*q.1 = 0
    dsimp [t]
    field_simp [ne_of_gt hd] <;> ring
  · change (1-t)*p.2+t*q.2 = 0
    rw [hpy,hqy]
    ring

theorem origin_mem_axis_segment_iff_opposite (p q : PlanarPoint ℝ)
    (hpy : p.2 = 0) (hqy : q.2 = 0) (hp0 : p.1 ≠ 0) (hq0 : q.1 ≠ 0) :
    (0 : PlanarPoint ℝ) ∈ segment ℝ p q ↔
      (p.1 < 0 ∧ 0 < q.1) ∨ (q.1 < 0 ∧ 0 < p.1) := by
  constructor
  · rintro ⟨u,v,hu,hv,hs,hpoint⟩
    have hx : u*p.1+v*q.1=0 := congrArg Prod.fst hpoint
    rcases lt_or_gt_of_ne hp0 with hp | hp <;> rcases lt_or_gt_of_ne hq0 with hq | hq
    · have hn := weighted_positive (-p.1) (-q.1) u v (by linarith) (by linarith) hu hv hs
      nlinarith
    · exact Or.inl ⟨hp,hq⟩
    · exact Or.inr ⟨hq,hp⟩
    · have hn := weighted_positive p.1 q.1 u v hp hq hu hv hs
      linarith
  · rintro (⟨hp,hq⟩ | ⟨hq,hp⟩)
    · exact origin_mem_axis_segment_of_opposite p q hpy hqy hp hq
    · rw [segment_symm]
      exact origin_mem_axis_segment_of_opposite q p hqy hpy hq hp

/-- The positive horizontal ray, as an actual subset of the real plane. -/
def positiveHorizontalRay : Set (PlanarPoint ℝ) := {z | z.2 = 0 ∧ 0 < z.1}

theorem triangle_positive_ray_parity (T : TrianglePatch)
    (ha : T.a.2 < 0) (hb : 0 < T.b.2) (hc : 0 < T.c.2)
    (horigin : (0 : PlanarPoint ℝ) ∉ T.boundary) :
    (T.boundary ∩ positiveHorizontalRay).ncard % 2 =
      if (0 : PlanarPoint ℝ) ∈ T.fill then 1 else 0 := by
  classical
  let p := horizontalCut T.a T.b
  let q := horizontalCut T.a T.c
  have hpy : p.2 = 0 := horizontalCut_y T.a T.b ha hb
  have hqy : q.2 = 0 := horizontalCut_y T.a T.c ha hc
  have hpq : p ≠ q := triangle_horizontal_cuts_ne T ha hb hc
  have hpB : p ∈ T.boundary := by
    have hm : p ∈ T.boundary ∩ {z : PlanarPoint ℝ | z.2=0} := by
      rw [triangle_boundary_horizontal_slice T ha hb hc]
      exact Set.mem_insert p _
    exact hm.1
  have hqB : q ∈ T.boundary := by
    have hm : q ∈ T.boundary ∩ {z : PlanarPoint ℝ | z.2=0} := by
      rw [triangle_boundary_horizontal_slice T ha hb hc]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton q)
    exact hm.1
  have hp0 : p.1 ≠ 0 := by
    intro hx
    have he : p = 0 := Prod.ext hx hpy
    exact horigin (he ▸ hpB)
  have hq0 : q.1 ≠ 0 := by
    intro hx
    have he : q = 0 := Prod.ext hx hqy
    exact horigin (he ▸ hqB)
  have hfill : (0 : PlanarPoint ℝ) ∈ T.fill ↔
      (p.1 < 0 ∧ 0 < q.1) ∨ (q.1 < 0 ∧ 0 < p.1) := by
    have hslice : (0 : PlanarPoint ℝ) ∈ T.fill ↔
        (0 : PlanarPoint ℝ) ∈ segment ℝ p q := by
      change (0 : PlanarPoint ℝ) ∈ convexHull ℝ {T.a,T.b,T.c} ↔ _
      rw [← triangle_horizontal_slice T.a T.b T.c ha hb hc]
      simp
    exact hslice.trans (origin_mem_axis_segment_iff_opposite p q hpy hqy hp0 hq0)
  have hset : T.boundary ∩ positiveHorizontalRay =
      (({p,q} : Finset (PlanarPoint ℝ)).filter (fun z => 0 < z.1) : Set (PlanarPoint ℝ)) := by
    have he : T.boundary ∩ positiveHorizontalRay =
        (T.boundary ∩ {z : PlanarPoint ℝ | z.2=0}) ∩ {z : PlanarPoint ℝ | 0<z.1} := by
      ext z
      simp only [positiveHorizontalRay, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
    rw [he, triangle_boundary_horizontal_slice T ha hb hc]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    rfl
  rw [hset, Set.ncard_coe_Finset]
  rcases lt_or_gt_of_ne hp0 with hp | hp <;> rcases lt_or_gt_of_ne hq0 with hq | hq
  · simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hp,
      not_lt_of_gt hq, hp, hq, hfill]
  · simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hp,
      not_lt_of_gt hq, hp, hq, hfill]
  · simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hp,
      not_lt_of_gt hq, hp, hq, hfill]
  · simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hp,
      not_lt_of_gt hq, hp, hq, hfill, hpq]

end
end DirectGLSSW.HOMFLY



