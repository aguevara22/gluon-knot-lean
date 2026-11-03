import DistinctVisitWindows

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem crossingVisitTime_mem_axis {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) :
    crossingVisitTime T c i ∈ secantAxisCuts T C := by
  have hk := visitPosition_lt_actual_period T (D.incoming c i)
  rw [hC] at hk
  exact secantAxisCuts_original_knot T C _ hk

theorem secantVisit_window_inside_quarter {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    crossingVisitTime T c i-1/4 < secantVisitLeft T c i ∧
      secantVisitRight T c i < crossingVisitTime T c i+1/4 := by
  have hε := secantMeshEpsilon_positive D
  have hl := secantMesh_inverse_window D c i (-secantMeshEpsilon D) ⟨le_rfl,by linarith⟩
  have hr := secantMesh_inverse_window D c i (2*secantMeshEpsilon D) ⟨by linarith,le_rfl⟩
  dsimp [secantVisitLeft,secantVisitRight]
  constructor <;> linarith [hl.1,hr.2]

theorem quarterGrid_in_visitWindow_eq_center {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2) (x : ℝ)
    (hx : x ∈ secantQuarterGrid T C)
    (hw : x ∈ Set.Icc (secantVisitLeft T c i) (secantVisitRight T c i)) :
    x=crossingVisitTime T c i := by
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
  have hb := secantVisit_window_inside_quarter T c i
  have hlo : ((4*visitPosition T (D.incoming c i)+1 : ℕ) : ℝ)<(k : ℝ) := by
    push_cast
    dsimp [crossingVisitTime] at hb
    linarith [hw.1,hb.1]
  have hhi : (k : ℝ)<((4*visitPosition T (D.incoming c i)+3 : ℕ) : ℝ) := by
    push_cast
    dsimp [crossingVisitTime] at hb
    linarith [hw.2,hb.2]
  have hln : 4*visitPosition T (D.incoming c i)+1<k := by exact_mod_cast hlo
  have hhn : k<4*visitPosition T (D.incoming c i)+3 := by exact_mod_cast hhi
  have he : k=4*visitPosition T (D.incoming c i)+2 := by omega
  rw [he]
  dsimp [crossingVisitTime]
  push_cast
  ring

/-- Exact actual cut classification inside one component visit window. -/
theorem secantAxisCuts_in_visitWindow_iff {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) (x : ℝ) :
    (x ∈ secantAxisCuts T C ∧ x ∈ Set.Icc (secantVisitLeft T c i) (secantVisitRight T c i)) ↔
      x=secantVisitLeft T c i ∨ x=crossingVisitTime T c i ∨ x=secantVisitRight T c i := by
  have he := secantVisit_endpoints_mem_axis T C c i hC
  have hs := secantVisit_endpoints_straddle T c i
  constructor
  · rintro ⟨hx,hw⟩
    rcases Finset.mem_union.mp hx with hq | hv
    · exact Or.inr (Or.inl (quarterGrid_in_visitWindow_eq_center T C c i x hq hw))
    · obtain ⟨⟨d,j⟩,hd,hx'⟩ := Finset.mem_biUnion.mp hv
      have hCd : componentOf D.continuation (D.incoming d j)=C := by
        simpa [secantComponentVisits] using hd
      by_cases hsame : (c,i)=(d,j)
      · have hcd : c=d := congrArg Prod.fst hsame
        have hij : i=j := congrArg Prod.snd hsame
        subst d
        subst j
        rcases Finset.mem_insert.mp hx' with hl | hr
        · exact Or.inl hl
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp hr))
      · have hgap := distinctVisitWindows_separated T c d i j hsame (hC.trans hCd.symm)
        have hds := secantVisit_endpoints_straddle T d j
        rcases Finset.mem_insert.mp hx' with hl | hr
        · rw [hl] at hw
          rcases hgap with hg | hg <;> exfalso <;> linarith [hw.1,hw.2,hds.1,hds.2]
        · have hr' := Finset.mem_singleton.mp hr
          rw [hr'] at hw
          rcases hgap with hg | hg <;> exfalso <;> linarith [hw.1,hw.2,hds.1,hds.2]
  · rintro (rfl | rfl | rfl)
    · exact ⟨he.1,le_rfl,by linarith [hs.1,hs.2]⟩
    · exact ⟨crossingVisitTime_mem_axis T C c i hC,hs.1.le,hs.2.le⟩
    · exact ⟨he.2,by linarith [hs.1,hs.2],le_rfl⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning




