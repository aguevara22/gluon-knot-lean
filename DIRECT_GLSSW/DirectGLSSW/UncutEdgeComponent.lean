import DirectGLSSW.PrimitiveEdgeGrouping
import DirectGLSSW.TwoStageRefinement

set_option autoImplicit false
namespace DirectGLSSW.UncutEdgeComponent
open PrimitiveEdgeGrouping PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem pairing_fixed_on_uncut_edge {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (e : Fin n) (S : Finset (PolygonCrossing P))
    (hOff : ∀ c ∈ S, ¬ Incident P e c) (x : PolygonEvent P)
    (hx : polygonEventEdge P x = e) : smoothingPairing P S x = x := by
  cases x with
  | inl a => rfl
  | inr v =>
    apply (smoothingPairing_visit_fixed_iff P S v).mpr
    intro hc
    apply hOff v.1 hc
    rcases v with ⟨c,b⟩
    cases b
    · exact Or.inl hx
    · exact Or.inr hx

/-- All original events on an uncut edge lie in the component of its anchor. -/
theorem incoming_component_on_uncut_edge {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (e : Fin n)
    (S : Finset (PolygonCrossing P)) (hOff : ∀ c ∈ S, ¬ Incident P e c)
    (x : PolygonEvent P) (hx : polygonEventEdge P x = e) :
    componentOf (smoothingIncomingPermutation P hG2 S) x =
      componentOf (smoothingIncomingPermutation P hG2 S) (Sum.inl e) := by
  classical
  letI : LinearOrder (Fin n ⊕ CrossingVisit P) := polygonEventOrder P hG2
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hG2
  let E := increasingEnumeration (PolygonEvent P)
  suffices h : ∀ k : ℕ, ∀ y : PolygonEvent P, (E.symm y).val = k →
      polygonEventEdge P y = e →
      componentOf (smoothingIncomingPermutation P hG2 S) y =
        componentOf (smoothingIncomingPermutation P hG2 S) (Sum.inl e) from
    h _ x rfl hx
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro y hy hey
    by_cases hya : y = Sum.inl e
    · rw [hya]
    have hay : (Sum.inl e : PolygonEvent P) < y := by
      cases y with
      | inl a => exact (hya (congrArg Sum.inl hey)).elim
      | inr v =>
        have h := polygonEvent_anchor_lt_visit P hG2 v
        have he : crossingVisitEdge P v = e := hey
        rw [← he]
        exact h
    let z := (polygonEventSuccessor P hG2)⁻¹ y
    have hzy : polygonEventSuccessor P hG2 z = y :=
      Equiv.apply_symm_apply (polygonEventSuccessor P hG2) y
    have hs := polygonEventSuccessor_order_spec P hG2 z
    rw [hzy] at hs
    have hzl : z < y := by
      rcases hs with hs | hs
      · exact hs.1
      · exact ((not_le_of_gt hay) (hs.2 (Sum.inl e))).elim
    have hze : polygonEventEdge P z = e := by
      rcases (polygonEvent_lt_iff P hG2 z y).mp hzl with hlt | ⟨heq,_⟩
      · have hza : z < (Sum.inl e : PolygonEvent P) := by
          apply (polygonEvent_lt_iff P hG2 z _).mpr
          change polygonEventEdge P z < polygonEventEdge P y at hlt
          rw [hey] at hlt
          exact Or.inl hlt
        rcases hs with hs | hs
        · exact ((not_le_of_gt hay) (hs.2 _ hza)).elim
        · exact ((not_le_of_gt hay) (hs.2 _)).elim
      · exact heq.trans hey
    have hzrank : (E.symm z).val < k := by
      rw [← hy]
      exact E.symm.strictMono hzl
    have hzcomp := ih _ hzrank z rfl hze
    have hin : smoothingIncomingPermutation P hG2 S z = y := by
      rw [smoothingIncomingPermutation_apply,pairing_fixed_on_uncut_edge P e S hOff z hze]
      exact hzy
    exact (hin ▸ componentOf_apply (smoothingIncomingPermutation P hG2 S) z).trans hzcomp

/-- Admissible on-edge completion cuts have both visits in the edge component. -/
theorem completion_visits_in_edge_component {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (e : Fin n) (U : OffEdgeSupport P hP e)
    (T : EdgeCompletion P hP e U) (c : PolygonCrossing P) (hc : c ∈ T.val) :
    componentOf (smoothingIncomingPermutation P hP.g2 U.val) (Sum.inr (c,false)) =
        componentOf (smoothingIncomingPermutation P hP.g2 U.val) (Sum.inl e) ∧
    componentOf (smoothingIncomingPermutation P hP.g2 U.val) (Sum.inr (c,true)) =
        componentOf (smoothingIncomingPermutation P hP.g2 U.val) (Sum.inl e) := by
  have hcU : c ∉ U.val := by
    intro h
    exact U.property.2 c h (T.property.1 c hc)
  have hElig := TwoStageRefinement.eligibleSupport_sdiff P hP.g2 U.val
    (U.val ∪ T.val) T.property.2 Finset.subset_union_left c
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hc,hcU⟩)
  have hi := T.property.1 c hc
  rcases hi with hleft | hright
  · have h := incoming_component_on_uncut_edge P hP.g2 e U.val U.property.2
      (Sum.inr (c,false)) hleft
    exact ⟨h,hElig.2.symm.trans h⟩
  · have h := incoming_component_on_uncut_edge P hP.g2 e U.val U.property.2
      (Sum.inr (c,true)) hright
    exact ⟨hElig.2.trans h,h⟩

/-- Spectator events are fixed by every admissible on-edge completion pairing. -/
theorem completion_pairing_fixes_spectator {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (e : Fin n) (U : OffEdgeSupport P hP e)
    (T : EdgeCompletion P hP e U) (x : PolygonEvent P)
    (hx : componentOf (smoothingIncomingPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingIncomingPermutation P hP.g2 U.val) (Sum.inl e)) :
    smoothingPairing P T.val x = x := by
  cases x with
  | inl a => rfl
  | inr v =>
    apply (smoothingPairing_visit_fixed_iff P T.val v).mpr
    intro hc
    obtain ⟨h₀,h₁⟩ := completion_visits_in_edge_component P hP e U T v.1 hc
    apply hx
    rcases v with ⟨c,b⟩
    cases b
    · exact h₀
    · exact h₁

theorem completion_incoming_fixes_spectator {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (e : Fin n) (U : OffEdgeSupport P hP e)
    (T : EdgeCompletion P hP e U) (x : PolygonEvent P)
    (hx : componentOf (smoothingIncomingPermutation P hP.g2 U.val) x ≠
      componentOf (smoothingIncomingPermutation P hP.g2 U.val) (Sum.inl e)) :
    smoothingIncomingPermutation P hP.g2 (U.val ∪ T.val) x =
      smoothingIncomingPermutation P hP.g2 U.val x := by
  rw [smoothingIncomingPermutation_union P hP.g2 U.val T.val (off_on_disjoint P hP e U T)]
  change smoothingIncomingPermutation P hP.g2 U.val (smoothingPairing P T.val x) = _
  rw [completion_pairing_fixes_spectator P hP e U T x hx]






end
end DirectGLSSW.UncutEdgeComponent
