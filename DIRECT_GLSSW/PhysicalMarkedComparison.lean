import PhysicalMarkedComparisonData
import ActualGeometricChildFactor
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.HOMFLY.PhysicalCursorComparison
open Coefficients PrincipalTurning PolygonDrawingBridge SmoothingCornerGeometry GeometricSmoothingWeights ExposedOpenPrimitive
open ActiveArc
open Cursor Split Primitive FiniteCalculation RetainedWords OpenCarrier AuxiliaryCarrierChart UniversalCarrierDomain
open CompatibleWords SingletonWords ChildRestartRecursion
open PhysicalParentHistory

/-- The actual finite physical recursion agrees with the actual framed marked
knot value. Every geometric step and both under branches are constructed;
only the genuine smaller-original-crossing strong induction hypothesis remains. -/
theorem physical_value_eq_marked_of_strongIH
    (hRI : GLSSWRootIndependence) {N : ℕ}
    (q : Fin (N+2) → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (hleft : ∀ i, 0<planarDet (cyclicTangent q i) (cyclicTangent q (cyclicSuccessor i)))
    (he : LeftExposed q 0) (hAux : auxiliaryGenericity q hq)
    (hstrongIH : SmallerPolygonCornerIH q)
    {n : ℕ} (p : Fin (n+2) → PlanarPoint ℝ) (D : Domain p)
    (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq p t h) :
    (-1 : ℚ)^(List.ofFn p).length*GammaM p D.hR D.hAux =
      (MarkedG.value t (MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) : ℚ) := by
  apply activeStep_induction (P := fun s => ∀ (D : Domain s.2) (t : MarkedParentState)
    (h : MarkedParentTrace (positivePolygonMarkedState q hq (initialAnchorTraversal q hq)) t)
    (C : GeometricCursor q hq s.2 t h),
    (-1 : ℚ)^(List.ofFn s.2).length*GammaM s.2 D.hR D.hAux =
      (MarkedG.value t (MarkedPolynomial.trace_nonempty h (positivePolygonEventDiagram_nArc_pos q hq)) : ℚ))
    ⟨n,p⟩ ?_ D t h C
  intro state ih
  rcases state with ⟨n,p⟩
  intro D t h C
  rcases TraversalClosure.actual_first_edge_selection p D.hleft with hn|hfirst|hfree
  · subst n
    rw [C.terminal_marked_value q hq he p t h,singleEdge_GammaM_one]
    norm_num [List.length_ofFn]
  · obtain ⟨c,hc⟩ := hfirst
    generalize hcut : c.val.2.val=a at *
    have ha : a≤n := by have := c.val.2.isLt;omega
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le ha
    by_cases ho : crossingOver p (polygonCrossingOfArc p c)=(polygonCrossingOfArc p c).val.1
    · obtain ⟨R,hRpos,HR⟩ := exists_over_cursor_radius q hq he p t h C D.hR c hc ho
      obtain ⟨ε,hε,hεR,hm0,hmc,hcp,hpb,hvalue,hG,hAux',hleft',hcore,hinc,hterminal⟩ :=
        exists_complete_first_over_step_within p D.hR D.hG D.hAux D.hleft hRI c hc hcut D.hcore
          D.L D.hL D.hT D.hinc D.hterminal ho R hRpos
      let ht0 : 0≤leftParameter p c+ε := (lt_trans (leftParameter_spec p c).1 hcp).le
      let hA := (regular_first_window_iff p D.hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
      let A : Domain (moveStart p (leftParameter p c+ε)) :=
        ⟨hA,hG,hAux',hleft',hcore,D.L,D.hL,D.hT,hinc,hterminal⟩
      obtain ⟨CA⟩ := HR ε hε hεR hpb
      exact hvalue.trans (ih _ (ActiveStep.afterFirst p D.hR c hc _ hcp hpb) A t h CA)
    · have hu : crossingUnder p (polygonCrossingOfArc p c)=(polygonCrossingOfArc p c).val.1 := by
        unfold crossingOver at ho
        unfold crossingUnder
        split_ifs with hsign
        · exact False.elim (ho (if_pos hsign))
        · rfl
      obtain ⟨hb,hg,⟨CP⟩,R,hRpos,HR⟩ := exists_under_cursors q hq he p t h C D.hR c hc hcut hu
      obtain ⟨ε,hε,hεR,hm0,hmc,hcp,hpb,hvalue,hpost,hPR,hPG,hPA,hPL,hPC,hML,hMT,hMI,hME⟩ :=
        exists_complete_first_under_step_within p D.hR D.hG D.hAux D.hleft hRI c hc hcut D.hcore
          D.L D.hL D.hT D.hinc D.hterminal hu R hRpos
      obtain ⟨hG,hAux',hleft',hcore,hinc,hterminal⟩ := hpost
      let ht0 : 0≤leftParameter p c+ε := (lt_trans (leftParameter_spec p c).1 hcp).le
      let hA := (regular_first_window_iff p D.hR c hc _ ht0 hpb).mpr (ne_of_gt hcp)
      let A : Domain (moveStart p (leftParameter p c+ε)) :=
        ⟨hA,hG,hAux',hleft',hcore,D.L,D.hL,D.hT,hinc,hterminal⟩
      let P : Domain (parent p c hcut) :=
        ⟨hPR,hPG,hPA,hPL,hPC,D.L ∘ suffixCarrierMap (a:=a) (b:=b),hML,hMT,hMI,hME⟩
      let selected := ((C.crossingEquiv he) c).val
      let switched := MarkedG.switchedState t selected hb hg
      let continuing := MarkedG.continuingState t selected hb hg
      let hs := switchedTrace h selected hb hg
      let hp := continuingTrace h selected hb hg
      obtain ⟨CA⟩ := HR ε hε hεR hpb
      have hAeq := ih _ (ActiveStep.afterFirst p D.hR c hc _ hcp hpb) A switched hs CA
      have hPeq := ih _ (ActiveStep.parent p D.hR c hc hcut) P continuing hp CP
      have hchild := C.detached_factor_of_strongIH q hq he hRI hleft hAux p t h D c hc hcut hu hstrongIH
      have hmarked := MarkedG.uniform_recurrence hRI q hq hleft he hAux t h selected hb hg
      have hmarkedQ := congrArg (fun z : ℤ => (z : ℚ)) hmarked
      simp only [Int.cast_sub,Int.cast_mul] at hmarkedQ
      calc
        _ = (-1 : ℚ)^(List.ofFn (moveStart p (leftParameter p c+ε))).length*
              GammaM (moveStart p (leftParameter p c+ε)) A.hR A.hAux -
            ((-1 : ℚ)^((Finset.univ.filter (fun i : Fin (a+1) =>
              0<planarDet (cyclicTangent (child p D.hR c hc.1 hcut) ((cyclicSuccessorPerm (a+1))⁻¹ i))
                (cyclicTangent (child p D.hR c hc.1 hcut) i))).card)*
              GeometricSmoothingWeights.separatingSmoothingSum (child p D.hR c hc.1 hcut)
                (child_cyclicGeneric_of_closedAuxiliary p D.hR c hc.1 hcut D.hAux)
                (child_auxiliaryGenericity p D.hR c hc hcut D.hAux))*
            ((-1 : ℚ)^(List.ofFn (parent p c hcut)).length*GammaM (parent p c hcut) P.hR P.hAux) := hvalue
        _ = (MarkedG.value switched (MarkedPolynomial.trace_nonempty hs (positivePolygonEventDiagram_nArc_pos q hq)) : ℚ)-
            (MarkedG.detachedValue t selected : ℚ)*
              (MarkedG.value continuing (MarkedPolynomial.trace_nonempty hp (positivePolygonEventDiagram_nArc_pos q hq)) : ℚ) := by
          rw [hAeq,hPeq,hchild]
        _ = _ := by rw [hmarkedQ];ring
  · obtain ⟨hn,hfree,hfirst⟩ := hfree
    obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨hvalue,hSR,hSA,hSL,hSC,hML,hMT,hMI,hME⟩ :=
      CornerProjector.firstEdgeFree_left_corner_step p D.hR hfree D.hAux hRI D.hleft D.hcore
        D.L D.hL D.hT D.hinc D.hterminal
    let S : Domain (suffix p) :=
      ⟨hSR,TraversalClosure.suffix_G1 p D.hG,hSA,hSL,hSC,
        D.L ∘ suffixCarrierMap (a:=1) (b:=b),hML,hMT,hMI,hME⟩
    have hfirst' : 0<planarDet (p 1-p 0) (p 2-p 1) := by
      have heq : (⟨2,by omega⟩ : Fin (1+b+2))=2 := by
        apply Fin.ext
        exact (Nat.mod_eq_of_lt (by omega : 2<1+b+2)).symm
      simpa only [heq] using hfirst
    obtain ⟨CS⟩ := exists_corner_cursor q hq he p t h C hfree
    exact hvalue.trans (ih _ (ActiveStep.cornerSuffix p D.hR hfirst' hfree) S t h CS)
end DirectGLSSW.HOMFLY.PhysicalCursorComparison
