import ActualRectangleSidePairing

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem basedComponent_period_positive {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : 0 < componentArcLength D (T.baseArc C).val := by
  have h := visitPosition_lt_actual_period T (T.baseArc C).val
  rw [(T.baseArc C).property] at h
  omega

/-- Actual finite next cell, derived from the literal cut set. -/
theorem secantAxis_successor_exists {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a : ℝ) (ha : a ∈ secantAxisCuts T C)
    (ham : a < (componentArcLength D (T.baseArc C).val : ℝ)) :
    ∃ b, secantAxisAdjacent T C a b := by
  let S := (secantAxisCuts T C).filter (fun b => a<b)
  have hS : S.Nonempty := ⟨_,Finset.mem_filter.mpr ⟨secantAxisCuts_period T C,ham⟩⟩
  let b := S.min' hS
  have hb : b ∈ secantAxisCuts T C ∧ a<b := Finset.mem_filter.mp (Finset.min'_mem S hS)
  refine ⟨b,ha,hb.1,hb.2,?_⟩
  intro u hu hau hub
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨hu,hau⟩
  have hbu : b≤u := Finset.min'_le S u huS
  linarith

/-- Actual finite previous cell, including the period endpoint. -/
theorem secantAxis_predecessor_exists {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (b : ℝ) (hb : b ∈ secantAxisCuts T C) (hb0 : 0<b) :
    ∃ a, secantAxisAdjacent T C a b := by
  let S := (secantAxisCuts T C).filter (fun a => a<b)
  have hS : S.Nonempty := ⟨_,Finset.mem_filter.mpr ⟨secantAxisCuts_zero T C,hb0⟩⟩
  let a := S.max' hS
  have ha : a ∈ secantAxisCuts T C ∧ a<b := Finset.mem_filter.mp (Finset.max'_mem S hS)
  refine ⟨a,ha.1,hb,ha.2,?_⟩
  intro u hu hau hub
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨hu,hub⟩
  have hua : u≤a := Finset.le_max' S u huS
  linarith

/-- Closed actual coverage. At a positive cut time choose the cell on its
left; at zero choose the first cell. No partition certificate is supplied. -/
theorem secantAxis_cells_cover_period {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val)) :
    ∃ a b, secantAxisAdjacent T C a b ∧ t ∈ Set.Icc a b := by
  by_cases ht0 : t=0
  · have hm : (0 : ℝ)<(componentArcLength D (T.baseArc C).val : ℝ) := by
      exact_mod_cast basedComponent_period_positive T C
    obtain ⟨b,hb⟩ := secantAxis_successor_exists T C 0 (secantAxisCuts_zero T C) hm
    exact ⟨0,b,hb,by rw [ht0]; exact ⟨le_rfl,hb.2.2.1.le⟩⟩
  · have htpos : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    let S := (secantAxisCuts T C).filter (fun a => a<t)
    have hS : S.Nonempty := ⟨_,Finset.mem_filter.mpr ⟨secantAxisCuts_zero T C,htpos⟩⟩
    let a := S.max' hS
    have ha : a ∈ secantAxisCuts T C ∧ a<t := Finset.mem_filter.mp (Finset.max'_mem S hS)
    obtain ⟨b,hb⟩ := secantAxis_successor_exists T C a ha.1 (lt_of_lt_of_le ha.2 ht.2)
    have htb : t≤b := by
      by_contra hn
      have hbS : b ∈ S := Finset.mem_filter.mpr ⟨hb.2.1,lt_of_not_ge hn⟩
      have hba : b≤a := Finset.le_max' S b hbS
      linarith [hb.2.2.1]
    exact ⟨a,b,hb,ha.2.le,htb⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning




