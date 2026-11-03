import VisitWindowCuts

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

theorem secantVisit_left_half_adjacent {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) :
    secantAxisAdjacent T C (secantVisitLeft T c i) (crossingVisitTime T c i) := by
  have he := secantVisit_endpoints_mem_axis T C c i hC
  have hs := secantVisit_endpoints_straddle T c i
  refine ⟨he.1,crossingVisitTime_mem_axis T C c i hC,hs.1,?_⟩
  intro x hx hL hv
  have hw : x ∈ Set.Icc (secantVisitLeft T c i) (secantVisitRight T c i) :=
    ⟨hL.le,by linarith [hs.2]⟩
  rcases (secantAxisCuts_in_visitWindow_iff T C c i hC x).mp ⟨hx,hw⟩ with h | h | h <;> linarith

theorem secantVisit_right_half_adjacent {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) :
    secantAxisAdjacent T C (crossingVisitTime T c i) (secantVisitRight T c i) := by
  have he := secantVisit_endpoints_mem_axis T C c i hC
  have hs := secantVisit_endpoints_straddle T c i
  refine ⟨crossingVisitTime_mem_axis T C c i hC,he.2,hs.2,?_⟩
  intro x hx hv hR
  have hw : x ∈ Set.Icc (secantVisitLeft T c i) (secantVisitRight T c i) :=
    ⟨by linarith [hs.1],hR.le⟩
  rcases (secantAxisCuts_in_visitWindow_iff T C c i hC x).mp ⟨hx,hw⟩ with h | h | h <;> linarith

/-- The two actual half-window cells are the only adjacent cells contained
in the actual visit window. -/
theorem secantAxis_cell_in_visitWindow_iff {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) (a b : ℝ) :
    (secantAxisAdjacent T C a b ∧ secantVisitLeft T c i≤a ∧ b≤secantVisitRight T c i) ↔
      (a=secantVisitLeft T c i ∧ b=crossingVisitTime T c i) ∨
      (a=crossingVisitTime T c i ∧ b=secantVisitRight T c i) := by
  have hs := secantVisit_endpoints_straddle T c i
  constructor
  · rintro ⟨hc,hL,hR⟩
    have ha : a ∈ Set.Icc (secantVisitLeft T c i) (secantVisitRight T c i) :=
      ⟨hL,by linarith [hc.2.2.1]⟩
    have hb : b ∈ Set.Icc (secantVisitLeft T c i) (secantVisitRight T c i) :=
      ⟨by linarith [hc.2.2.1],hR⟩
    rcases (secantAxisCuts_in_visitWindow_iff T C c i hC a).mp ⟨hc.1,ha⟩ with rfl | rfl | rfl <;>
      rcases (secantAxisCuts_in_visitWindow_iff T C c i hC b).mp ⟨hc.2.1,hb⟩ with rfl | rfl | rfl
    all_goals try exact Or.inl ⟨rfl,rfl⟩
    all_goals try exact Or.inr ⟨rfl,rfl⟩
    all_goals try (exfalso; exact hc.2.2.2 _ (crossingVisitTime_mem_axis T C c i hC) hs.1 hs.2)
    all_goals exfalso; linarith [hc.2.2.1,hs.1,hs.2]
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨secantVisit_left_half_adjacent T C c i hC,le_rfl,hs.2.le⟩
    · exact ⟨secantVisit_right_half_adjacent T C c i hC,hs.1.le,le_rfl⟩

end DirectGLSSW.HOMFLY.PrincipalTurning



