import FiniteSecantCells

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
open scoped Classical

theorem secantVisit_endpoints_mem_axis {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i : Fin 2)
    (hC : componentOf D.continuation (D.incoming c i)=C) :
    secantVisitLeft T c i ∈ secantAxisCuts T C ∧ secantVisitRight T c i ∈ secantAxisCuts T C := by
  have hv : (c,i) ∈ secantComponentVisits T C := by simp [secantComponentVisits,hC]
  constructor
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨(c,i),hv,by simp⟩
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨(c,i),hv,by simp⟩

theorem secantVisit_endpoints_straddle {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    secantVisitLeft T c i < crossingVisitTime T c i ∧
      crossingVisitTime T c i < secantVisitRight T c i := by
  have hε := secantMeshEpsilon_positive D
  have hα := outgoingTangentScale_pos D c i
  have hp : 0 < outgoingTangentScale D c i*(2*secantMeshEpsilon D) :=
    mul_pos hα (mul_pos (by norm_num) hε)
  simp only [secantVisitLeft,secantVisitRight,crossingStarCoordinateInverse,
    if_pos (by linarith : -secantMeshEpsilon D ≤ 0),
    if_neg (by linarith : ¬2*secantMeshEpsilon D ≤ 0)]
  constructor <;> linarith

/-- Removal is a literal finite crossing-window containment test, not a
zero-free certificate. Both branch orders are indexed by actual visit time. -/
def secantRectangleInsideStar {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (a b u v : ℝ) : Prop :=
  ∃ c : Fin D.nCrossing, ∃ i j : Fin 2, i ≠ j ∧
    componentOf D.continuation (D.incoming c i)=C ∧
    componentOf D.continuation (D.incoming c j)=C ∧
    crossingVisitTime T c i < crossingVisitTime T c j ∧
    secantVisitLeft T c i ≤ a ∧ b ≤ secantVisitRight T c i ∧
    secantVisitLeft T c j ≤ u ∧ v ≤ secantVisitRight T c j

def secantRetainedRectangles {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((secantAxisCells T C).product (secantAxisCells T C)).filter (fun r =>
    r.1.2 < r.2.1 ∧
    ¬(r.1.2 ≤ 1/4 ∧ (componentArcLength D (T.baseArc C).val : ℝ)-1/4 ≤ r.2.1) ∧
    ¬secantRectangleInsideStar T C r.1.1 r.1.2 r.2.1 r.2.2)

/-- Every closed retained actual rectangle avoids zero. The removals derive
from the actual global classification, including the periodic base-corner. -/
theorem secantRetainedRectangle_nonzero {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u v s t : ℝ)
    (hr : ((a,b),(u,v)) ∈ secantRetainedRectangles T C)
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc u v) :
    basedUniformSecant T C s t ≠ 0 := by
  have hfilter := Finset.mem_filter.mp hr
  obtain ⟨hcell1,hcell2⟩ := Finset.mem_product.mp hfilter.1
  have h1 : secantAxisAdjacent T C a b := (Finset.mem_filter.mp hcell1).2
  have h2 : secantAxisAdjacent T C u v := (Finset.mem_filter.mp hcell2).2
  have hpred : b<u ∧ ¬(b ≤ 1/4 ∧ (componentArcLength D (T.baseArc C).val : ℝ)-1/4 ≤ u) ∧
      ¬secantRectangleInsideStar T C a b u v := hfilter.2
  have ha := secantAxisCuts_bounds T C a h1.1
  have hb := secantAxisCuts_bounds T C b h1.2.1
  have hu := secantAxisCuts_bounds T C u h2.1
  have hv := secantAxisCuts_bounds T C v h2.2.1
  have hs' : s ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val) :=
    ⟨le_trans ha.1 hs.1,le_trans hs.2 hb.2⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val) :=
    ⟨le_trans hu.1 ht.1,le_trans ht.2 hv.2⟩
  have hst : s<t := by linarith [hs.2,ht.1,hpred.1]
  intro hz
  rcases (basedUniformSecant_global_zero_iff T C s t hs' ht').mp hz with
    heq | ⟨hs0,htm⟩ | ⟨hsm,ht0⟩ | ⟨c,i,j,hij,hCi,hCj,hsi,htj⟩
  · linarith
  · have ha0 : a=0 := by linarith [ha.1,hs.1]
    have hvm : v=(componentArcLength D (T.baseArc C).val : ℝ) := by linarith [hv.2,ht.2]
    have hw1 := secantAxisAdjacent_width T C a b h1
    have hw2 := secantAxisAdjacent_width T C u v h2
    exact hpred.2.1 ⟨by linarith,by linarith⟩
  · linarith [hs'.1,ht'.1]
  · have hiMem := secantVisit_endpoints_mem_axis T C c i hCi
    have hjMem := secantVisit_endpoints_mem_axis T C c j hCj
    have hiStr := secantVisit_endpoints_straddle T c i
    have hjStr := secantVisit_endpoints_straddle T c j
    have hsi' : crossingVisitTime T c i ∈ Set.Icc a b := by simpa only [hsi] using hs
    have htj' : crossingVisitTime T c j ∈ Set.Icc u v := by simpa only [htj] using ht
    have hi := secantAxisAdjacent_window_containment T C a b _ _ _ h1 hiMem.1 hiMem.2 hsi' hiStr.1 hiStr.2
    have hj := secantAxisAdjacent_window_containment T C u v _ _ _ h2 hjMem.1 hjMem.2 htj' hjStr.1 hjStr.2
    apply hpred.2.2
    exact ⟨c,i,j,hij,hCi,hCj,by linarith,hi.1,hi.2,hj.1,hj.2⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning



