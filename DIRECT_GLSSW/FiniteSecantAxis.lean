import OrderedCrossingRectangle
import UniformPLGlobalZero
import Mathlib.Data.Finset.Max

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
open scoped Classical

def secantMeshRadiusSet (D : PLLinkDiagram) : Finset ℝ :=
  insert (1/8) (Finset.univ.image (crossingStarStrictRadius D))

theorem secantMeshRadiusSet_nonempty (D : PLLinkDiagram) : (secantMeshRadiusSet D).Nonempty :=
  Finset.insert_nonempty _ _

def secantMeshEpsilon (D : PLLinkDiagram) : ℝ :=
  (secantMeshRadiusSet D).min' (secantMeshRadiusSet_nonempty D) / 2

theorem secantMesh_min_positive (D : PLLinkDiagram) :
    0 < (secantMeshRadiusSet D).min' (secantMeshRadiusSet_nonempty D) := by
  apply (Finset.lt_min'_iff _ _).mpr
  intro r hr
  simp only [secantMeshRadiusSet,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hr
  rcases hr with rfl | ⟨c,rfl⟩
  · norm_num
  · exact crossingStarStrictRadius_pos D c

theorem secantMeshEpsilon_positive (D : PLLinkDiagram) : 0 < secantMeshEpsilon D :=
  div_pos (secantMesh_min_positive D) (by norm_num)

theorem secantMeshEpsilon_lt_radius (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    secantMeshEpsilon D < crossingStarStrictRadius D c := by
  have hm := secantMesh_min_positive D
  have hle : (secantMeshRadiusSet D).min' (secantMeshRadiusSet_nonempty D) ≤
      crossingStarStrictRadius D c := Finset.min'_le _ _ (by simp [secantMeshRadiusSet])
  unfold secantMeshEpsilon
  linarith

theorem secantMeshEpsilon_le_sixteenth (D : PLLinkDiagram) : secantMeshEpsilon D ≤ 1/16 := by
  have hle : (secantMeshRadiusSet D).min' (secantMeshRadiusSet_nonempty D) ≤ (1/8 : ℝ) :=
    Finset.min'_le _ _ (by simp [secantMeshRadiusSet])
  unfold secantMeshEpsilon
  linarith

def secantComponentVisits {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    Finset (Fin D.nCrossing × Fin 2) :=
  Finset.univ.filter (fun ci => componentOf D.continuation (D.incoming ci.1 ci.2)=C)

def secantVisitLeft {D : PLLinkDiagram} (T : BasedTraversal D) (c : Fin D.nCrossing) (i : Fin 2) : ℝ :=
  crossingVisitTime T c i + crossingStarCoordinateInverse D c i (-secantMeshEpsilon D)

def secantVisitRight {D : PLLinkDiagram} (T : BasedTraversal D) (c : Fin D.nCrossing) (i : Fin 2) : ℝ :=
  crossingVisitTime T c i + crossingStarCoordinateInverse D c i (2*secantMeshEpsilon D)

theorem secantVisit_endpoints_inside {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) :
    secantVisitLeft T c i ∈ Set.Ioo (0 : ℝ) (componentArcLength D (T.baseArc C).val) ∧
      secantVisitRight T c i ∈ Set.Ioo (0 : ℝ) (componentArcLength D (T.baseArc C).val) := by
  have hε := secantMeshEpsilon_positive D
  have hr := secantMeshEpsilon_lt_radius D c
  have hl := crossingVisitTime_window_inside_period T c i (-secantMeshEpsilon D)
    (by constructor <;> linarith)
  have hh := crossingVisitTime_window_inside_period T c i (2*secantMeshEpsilon D)
    (by constructor <;> linarith)
  rw [hC] at hl hh
  exact ⟨hl,hh⟩

def secantComponentWindowCuts {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) : Finset ℝ :=
  (secantComponentVisits T C).biUnion (fun ci => {secantVisitLeft T ci.1 ci.2,secantVisitRight T ci.1 ci.2})

def secantQuarterGrid {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) : Finset ℝ :=
  (Finset.range (4*componentArcLength D (T.baseArc C).val+1)).image (fun k : ℕ => (k : ℝ)/4)

def secantAxisCuts {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) : Finset ℝ :=
  secantQuarterGrid T C ∪ secantComponentWindowCuts T C

theorem secantAxisCuts_bounds {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (x : ℝ) (hx : x ∈ secantAxisCuts T C) :
    x ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val) := by
  rcases Finset.mem_union.mp hx with hq | hw
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hq
    simp only [Finset.mem_range] at hk
    have hk' : k ≤ 4*componentArcLength D (T.baseArc C).val := by omega
    have hkr : (k : ℝ) ≤ 4*(componentArcLength D (T.baseArc C).val : ℝ) := by exact_mod_cast hk'
    constructor
    · positivity
    · exact (div_le_iff₀ (by norm_num : (0 : ℝ)<4)).mpr (by simpa only [mul_comm] using hkr)
  · obtain ⟨⟨c,i⟩,hv,hx⟩ := Finset.mem_biUnion.mp hw
    have hC : componentOf D.continuation (D.incoming c i)=C := by simpa [secantComponentVisits] using hv
    have he := secantVisit_endpoints_inside T C c i hC
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]
      exact ⟨he.1.1.le,he.1.2.le⟩
    · have h' := Finset.mem_singleton.mp h
      rw [h']
      exact ⟨he.2.1.le,he.2.2.le⟩

theorem secantAxisCuts_zero {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    (0 : ℝ) ∈ secantAxisCuts T C := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨0,by simp,by norm_num⟩

theorem secantAxisCuts_period {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    (componentArcLength D (T.baseArc C).val : ℝ) ∈ secantAxisCuts T C := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨4*componentArcLength D (T.baseArc C).val,by simp,?_⟩
  push_cast
  ring

theorem secantAxisCuts_original_knot {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (k : ℕ) (hk : k < componentArcLength D (T.baseArc C).val) :
    (k : ℝ)+1/2 ∈ secantAxisCuts T C := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨4*k+2,?_,?_⟩
  · simp only [Finset.mem_range]
    omega
  · push_cast
    ring

end
end DirectGLSSW.HOMFLY.PrincipalTurning









