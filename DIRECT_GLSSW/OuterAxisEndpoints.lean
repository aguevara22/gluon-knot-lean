import StarCellBoundarySeparation

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem secantComponentWindowCuts_quarter_margin {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (x : ℝ)
    (hx : x ∈ secantComponentWindowCuts T C) :
    1/4<x ∧ x<(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
  obtain ⟨⟨c,i⟩,hm,hx⟩ := Finset.mem_biUnion.mp hx
  have hC : componentOf D.continuation (D.incoming c i)=C := by
    exact (Finset.mem_filter.mp hm).2
  have he := secantMeshEpsilon_positive D
  rcases Finset.mem_insert.mp hx with rfl | hx
  · have h := secantMesh_visit_window_inside_margin T c i (-secantMeshEpsilon D)
      ⟨le_rfl,by linarith⟩
    rw [hC] at h
    exact h
  · have hx := Finset.mem_singleton.mp hx
    subst x
    have h := secantMesh_visit_window_inside_margin T c i (2*secantMeshEpsilon D)
      ⟨by linarith,le_rfl⟩
    rw [hC] at h
    exact h

theorem secantAxisCuts_end_gaps {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (x : ℝ) (hx : x ∈ secantAxisCuts T C) :
    x=0 ∨ x=(componentArcLength D (T.baseArc C).val : ℝ) ∨
      (1/4≤x ∧ x≤(componentArcLength D (T.baseArc C).val : ℝ)-1/4) := by
  rcases Finset.mem_union.mp hx with hq | hw
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hq
    have hkn : k≤4*componentArcLength D (T.baseArc C).val := by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases h0 : k=0
    · left; simp only [h0,Nat.cast_zero,zero_div]
    · right
      by_cases hm : k=4*componentArcLength D (T.baseArc C).val
      · left; rw [hm]; push_cast; ring
      · right
        have hklo : (1 : ℝ)≤(k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        have hkup : (k : ℝ)+1≤4*(componentArcLength D (T.baseArc C).val : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_ne hkn hm)
        constructor <;> linarith
  · have h := secantComponentWindowCuts_quarter_margin T C x hw
    exact Or.inr (Or.inr ⟨h.1.le,h.2.le⟩)

theorem secantAxisAdjacent_initial_endpoint {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (b : ℝ) (h : secantAxisAdjacent T C 0 b) : b=1/4 := by
  have hb := secantAxisCuts_bounds T C b h.2.1
  have hmnat : 0<componentArcLength D (T.baseArc C).val := by
    exact_mod_cast lt_of_lt_of_le h.2.2.1 hb.2
  have hm : (1 : ℝ)≤(componentArcLength D (T.baseArc C).val : ℝ) := by
    exact_mod_cast hmnat
  have hq := secantAxisCuts_quarter T C 1 (by omega)
  norm_num only [Nat.cast_one,one_div] at hq
  have hlo : 1/4≤b := by
    rcases secantAxisCuts_end_gaps T C b h.2.1 with hz | he | hi
    · linarith [h.2.2.1]
    · linarith
    · exact hi.1
  have hhi : b≤1/4 := by
    by_contra hn
    exact h.2.2.2 _ hq (by norm_num) (lt_of_not_ge hn)
  exact le_antisymm hhi hlo

theorem secantAxisAdjacent_final_endpoint {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a : ℝ)
    (h : secantAxisAdjacent T C a (componentArcLength D (T.baseArc C).val : ℝ)) :
    a=(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
  have ha := secantAxisCuts_bounds T C a h.1
  have hmnat : 0<componentArcLength D (T.baseArc C).val := by
    exact_mod_cast lt_of_le_of_lt ha.1 h.2.2.1
  have hm : (1 : ℝ)≤(componentArcLength D (T.baseArc C).val : ℝ) := by
    exact_mod_cast hmnat
  have hq := secantAxisCuts_quarter T C (4*componentArcLength D (T.baseArc C).val-1) (by omega)
  have hqeq : ((4*componentArcLength D (T.baseArc C).val-1 : ℕ) : ℝ)/4 =
      (componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hqeq] at hq
  have hhi : a≤(componentArcLength D (T.baseArc C).val : ℝ)-1/4 := by
    rcases secantAxisCuts_end_gaps T C a h.1 with hz | he | hi
    · linarith
    · linarith [h.2.2.1]
    · exact hi.2
  have hlo : (componentArcLength D (T.baseArc C).val : ℝ)-1/4≤a := by
    by_contra hn
    exact h.2.2.2 _ hq (lt_of_not_ge hn) (by linarith)
  exact le_antisymm hhi hlo

end
end DirectGLSSW.HOMFLY.PrincipalTurning




