import SM.WeakGeometry

/-! The geometric properties needed to read actual crossings and visits.
This auxiliary predicate does not require nonzero turns or G1. It is proved
from the original hypotheses before being used at nongeneric centres. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

def CrossingGeometry (P : LabelledTuple n) : Prop :=
  (∀ i, edge P i ≠ 0) ∧
  (∀ i j, remote i j → ∀ x, x ∈ edgeSegment P i → x ∈ edgeSegment P j →
    x ∈ edgeInterior P i ∧ x ∈ edgeInterior P j ∧ det (edge P i) (edge P j) ≠ 0) ∧
  G2 P

theorem weak_crossingGeometry (h : WeakGeneric P) : CrossingGeometry P := by
  refine ⟨h.1, ?_, h.2.2.2.2⟩
  intro i j hr x hi hj
  exact ⟨remote_closed_point_interior h.2.2.1 hr hi hj,
    remote_closed_point_interior h.2.2.1 (remote_symm hr) hj hi,
    (h.2.2.2.1 i j hr).1 x hi hj⟩

theorem generic_crossingGeometry (hn : 3 ≤ n) (h : Generic P) : CrossingGeometry P :=
  weak_crossingGeometry (generic_implies_weak hn h)

theorem crossingPoint_interior_of_geometry (h : CrossingGeometry P)
    (c : Crossing P) (k : ZMod n) (hk : k ∈ c.val) :
    crossingPoint c ∈ edgeInterior P k := by
  obtain ⟨i, j, hs, hr, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hm := h.2.1 i j hr (crossingPoint c) (crossingPoint_mem c i hi)
    (crossingPoint_mem c j hj)
  rw [hs] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact hm.1
  · exact hm.2.1

theorem crossingPoint_unique_of_geometry (h : CrossingGeometry P)
    (c : Crossing P) (x : Plane) (hx : ∀ i ∈ c.val, x ∈ edgeSegment P i) :
    x = crossingPoint c := by
  obtain ⟨i, j, hs, hr, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hm := h.2.1 i j hr (crossingPoint c) (crossingPoint_mem c i hi)
    (crossingPoint_mem c j hj)
  exact transverse_segments_unique hm.2.2 (hx i hi) (hx j hj)
    (crossingPoint_mem c i hi) (crossingPoint_mem c j hj)

theorem crossingParameter_interior_of_geometry (h : CrossingGeometry P)
    (c : Crossing P) (i : ZMod n) (hi : i ∈ c.val) :
    0 < crossingParameter c i hi ∧ crossingParameter c i hi < 1 := by
  obtain ⟨t, ht0, ht1, ht⟩ := crossingPoint_interior_of_geometry h c i hi
  have he := (crossingParameter_spec c i hi).2.2.symm.trans ht
  have hp := edgePoint_injective (h.1 i) he
  rw [hp]
  exact ⟨ht0, ht1⟩

theorem crossingPoint_injective_of_geometry (h : CrossingGeometry P) :
    Function.Injective (@crossingPoint n P) := by
  intro c d hpoint
  have support_subset (c d : Crossing P) (heq : crossingPoint c = crossingPoint d) :
      c.val ⊆ d.val := by
    obtain ⟨i, j, hs, hr, _⟩ := d.property
    have hi : i ∈ d.val := by rw [hs]; simp
    have hj : j ∈ d.val := by rw [hs]; simp
    intro k hk
    by_contra hnot
    have hki : k ≠ i := by intro he; subst k; exact hnot hi
    have hkj : k ≠ j := by intro he; subst k; exact hnot hj
    have hxk := crossingPoint_interior_of_geometry h c k hk
    rw [heq] at hxk
    apply h.2.2
    exact ⟨i, j, k, crossingPoint d, (remote_endpoints i j hr).1.symm,
      hkj.symm, hki.symm, crossingPoint_interior_of_geometry h d i hi,
      crossingPoint_interior_of_geometry h d j hj, hxk⟩
  apply Subtype.ext
  exact Finset.Subset.antisymm (support_subset c d hpoint) (support_subset d c hpoint.symm)

end SM
