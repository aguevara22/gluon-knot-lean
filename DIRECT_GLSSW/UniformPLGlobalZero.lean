import UniformPLCellCoincidence
import UniformPLSourceIncidence
import UniformPLIntegerVisit

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv PermutationOrbits

theorem basedUniform_same_arc_parameter (D : PLLinkDiagram) (e : Fin D.nArc)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (componentArcLength D e))
    (ht : t ∈ Set.Icc (0 : ℝ) (componentArcLength D e))
    (ha : (D.continuation ^ basedArcIndex s) e = (D.continuation ^ basedArcIndex t) e)
    (hf : Int.fract (s+1/2)=Int.fract (t+1/2)) :
    s=t ∨ (s=0 ∧ t=(componentArcLength D e : ℝ)) ∨
      (s=(componentArcLength D e : ℝ) ∧ t=0) := by
  have hsdec := basedArcIndex_decomposition (componentArcLength D e) s hs
  have htdec := basedArcIndex_decomposition (componentArcLength D e) t ht
  have hks := (basedUniform_address_bounds (componentArcLength D e) s hs).2
  have hkt := (basedUniform_address_bounds (componentArcLength D e) t ht).2
  rcases (continuation_pow_closed_period_iff D e (basedArcIndex s) (basedArcIndex t) hks hkt).mp ha with h | ⟨hk,hl⟩ | ⟨hk,hl⟩
  · rw [h] at hsdec
    exact Or.inl (by linarith)
  · rw [hk] at hsdec
    rw [hl] at htdec
    norm_num only [Nat.cast_zero,zero_add] at hsdec
    exact Or.inr (Or.inl ⟨by linarith [hs.1,ht.2],by linarith [hs.1,ht.2]⟩)
  · rw [hk] at hsdec
    rw [hl] at htdec
    norm_num only [Nat.cast_zero,zero_add] at htdec
    exact Or.inr (Or.inr ⟨by linarith [hs.2,ht.1],by linarith [hs.2,ht.1]⟩)

/-- All zeros on the literal closed based period square: diagonal, both
midpoint seam pairs, or actual distinct crossing visits on this component. -/
theorem basedUniformPLCurve_global_coincidence {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val))
    (ht : t ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val)) :
    basedUniformPLCurve T C s = basedUniformPLCurve T C t ↔
      s=t ∨ (s=0 ∧ t=(componentArcLength D (T.baseArc C).val : ℝ)) ∨
      (s=(componentArcLength D (T.baseArc C).val : ℝ) ∧ t=0) ∨
      ∃ c : Fin D.nCrossing, ∃ i j : Fin 2, i ≠ j ∧
        componentOf D.continuation (D.incoming c i)=C ∧
        componentOf D.continuation (D.incoming c j)=C ∧
        s=crossingVisitTime T c i ∧ t=crossingVisitTime T c j := by
  let e := (T.baseArc C).val
  have same (ha : (D.continuation ^ basedArcIndex s) e = (D.continuation ^ basedArcIndex t) e)
      (hf : Int.fract (s+1/2)=Int.fract (t+1/2)) :
      s=t ∨ (s=0 ∧ t=(componentArcLength D e : ℝ)) ∨
      (s=(componentArcLength D e : ℝ) ∧ t=0) :=
    basedUniform_same_arc_parameter D e s t hs ht ha hf
  constructor
  · intro he
    change uniformPLCurve D e (s+1/2)=uniformPLCurve D e (t+1/2) at he
    have hc := (uniformPLCurve_cell_coincidence D e (s+1/2) (t+1/2)).mp he
    rw [← (basedUniform_address_bounds (componentArcLength D e) s hs).1,
      ← (basedUniform_address_bounds (componentArcLength D e) t ht).1,zpow_natCast,zpow_natCast] at hc
    rcases hc with ⟨ha,hf⟩ | ⟨hfs,hft,hsource⟩
    · rcases same ha hf with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · by_cases ha : (D.continuation ^ basedArcIndex s) e = (D.continuation ^ basedArcIndex t) e
      · rcases same ha (hfs.trans hft.symm) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · obtain ⟨c,i,j,hij,hi,hj⟩ := actual_distinct_sources_crossing D _ _ ha hsource
        obtain ⟨hCi,hsi⟩ := basedUniform_integer_visit_of_outgoing T C s hs hfs c i hi
        obtain ⟨hCj,htj⟩ := basedUniform_integer_visit_of_outgoing T C t ht hft c j hj
        exact Or.inr (Or.inr (Or.inr ⟨c,i,j,hij,hCi,hCj,hsi,htj⟩))
  · have hseam : basedUniformPLCurve T C (componentArcLength D e : ℝ) =
        basedUniformPLCurve T C 0 := by
      simpa only [zero_add] using basedUniformPLCurve_periodic T C 0
    have visit (c : Fin D.nCrossing) (i : Fin 2)
        (hC : componentOf D.continuation (D.incoming c i)=C) :
        basedUniformPLCurve T C (crossingVisitTime T c i) = D.vertexPoint (D.crossingVertex c) := by
      have h := basedUniformPLCurve_crossing_star T c i 0 (by constructor <;> norm_num)
      rw [hC] at h
      simpa [crossingStarPoint,affinePoint_one] using h
    rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨c,i,j,_,hCi,hCj,rfl,rfl⟩)
    · rfl
    · exact hseam.symm
    · exact hseam
    · exact (visit c i hCi).trans (visit c j hCj).symm

noncomputable def basedUniformSecant {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (s t : ℝ) : ℂ :=
  Complex.equivRealProd.symm (basedUniformPLCurve T C t - basedUniformPLCurve T C s)

theorem basedUniformSecant_global_zero_iff {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val))
    (ht : t ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val)) :
    basedUniformSecant T C s t = 0 ↔
      s=t ∨ (s=0 ∧ t=(componentArcLength D (T.baseArc C).val : ℝ)) ∨
      (s=(componentArcLength D (T.baseArc C).val : ℝ) ∧ t=0) ∨
      ∃ c : Fin D.nCrossing, ∃ i j : Fin 2, i ≠ j ∧
        componentOf D.continuation (D.incoming c i)=C ∧
        componentOf D.continuation (D.incoming c j)=C ∧
        s=crossingVisitTime T c i ∧ t=crossingVisitTime T c j := by
  constructor
  · intro hz
    have h := congrArg Complex.equivRealProd hz
    change basedUniformPLCurve T C t - basedUniformPLCurve T C s = 0 at h
    exact (basedUniformPLCurve_global_coincidence T C s t hs ht).mp (sub_eq_zero.mp h).symm
  · intro h
    have hp := (basedUniformPLCurve_global_coincidence T C s t hs ht).mpr h
    unfold basedUniformSecant
    rw [hp,sub_self]
    rfl

end DirectGLSSW.HOMFLY.PrincipalTurning




