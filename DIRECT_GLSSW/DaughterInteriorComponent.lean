import DaughterOpenParameter
import DaughterCrossingAvoidance

set_option autoImplicit false
namespace DirectGLSSW.DaughterInteriorComponent
open DaughterFirstReturn DaughterNoRetainedInterior DaughterOpenParameter PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An original interval containing no retained event after its start remains
one outgoing-dart component; the proof uses the actual ordered predecessor. -/
theorem dart_component_of_interval_no_retained {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hG2 : cyclicNoTripleIntersections P) (S : Finset (PolygonCrossing P))
    (x y : PolygonEvent P) (hxy : (polygonEventOrder P hG2).le x y)
    (hno : ∀ z, (polygonEventOrder P hG2).lt x z → (polygonEventOrder P hG2).le z y →
      ¬ retainedCorner P S z) :
    componentOf (smoothingDartPermutation P hG2 S) y =
      componentOf (smoothingDartPermutation P hG2 S) x := by
  classical
  letI : LinearOrder (Fin n ⊕ CrossingVisit P) := polygonEventOrder P hG2
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hG2
  let E := increasingEnumeration (PolygonEvent P)
  suffices h : ∀ k : ℕ, ∀ y : PolygonEvent P, (E.symm y).val = k → x ≤ y →
      (∀ z, x < z → z ≤ y → ¬ retainedCorner P S z) →
      componentOf (smoothingDartPermutation P hG2 S) y =
        componentOf (smoothingDartPermutation P hG2 S) x from h _ y rfl hxy hno
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro y hy hxy hno
    rcases eq_or_lt_of_le hxy with rfl | hxy
    · rfl
    let z := (polygonEventSuccessor P hG2)⁻¹ y
    have hzy : polygonEventSuccessor P hG2 z = y :=
      Equiv.apply_symm_apply (polygonEventSuccessor P hG2) y
    have hs := polygonEventSuccessor_order_spec P hG2 z
    rw [hzy] at hs
    have hzl : z < y := by
      rcases hs with hs | hs
      · exact hs.1
      · exact ((not_le_of_gt hxy) (hs.2 x)).elim
    have hxz : x ≤ z := by
      apply le_of_not_gt
      intro hzx
      rcases hs with hs | hs
      · exact (not_le_of_gt hxy) (hs.2 x hzx)
      · exact (not_le_of_gt hxy) (hs.2 x)
    have hzrank : (E.symm z).val < k := by
      rw [← hy]
      exact E.symm.strictMono hzl
    have hzcomp := ih _ hzrank z rfl hxz (fun w hxw hwz => hno w hxw (hwz.trans hzl.le))
    have hdart : smoothingDartPermutation P hG2 S z = y := by
      rw [smoothingDartPermutation_apply,hzy,pairing_fixes_noncorner P S y (hno y hxy le_rfl)]
    exact (hdart ▸ componentOf_apply (smoothingDartPermutation P hG2 S) z).trans hzcomp

/-- Every actual original event in a daughter open edge belongs to that daughter. -/
theorem event_in_daughter_edge_component {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (y : PolygonEvent P) (hye : polygonEventEdge P y = daughterCarrier P hP.g2 S root i)
    (hy : edgeInterior (daughterVertex P hP.g2 S root) i (polygonEventPoint P y)) :
    componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root := by
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hP.g2
  let c := cornerEnumeration P hP.g2 S root i
  let x := orbitEventAt P hP.g2 S root c.val
  let e := daughterCarrier P hP.g2 S root i
  have hxe : polygonEventEdge P x = e := rfl
  have hye' : polygonEventEdge P y = e := hye
  have hparam := (eventPoint_mem_daughter_edge_iff P hP S root hroot i y hye).mp hy
  have hxy : x < y := (polygonEvent_sameEdge_lt_iff P hP.g2 x y (hxe.trans hye'.symm)).mpr hparam.1
  have hno : ∀ z, x < z → z ≤ y → ¬ retainedCorner P S z := by
    intro z hxz hzy hzret
    have hze : polygonEventEdge P z = e := by
      have h₁ := polygonEventEdge_monotone P hP.g2 hxz.le
      have h₂ := polygonEventEdge_monotone P hP.g2 hzy
      rw [hxe] at h₁
      rw [hye'] at h₂
      exact le_antisymm h₂ h₁
    have hpz : polygonEventParameter P x < polygonEventParameter P z :=
      (polygonEvent_sameEdge_lt_iff P hP.g2 x z (hxe.trans hze.symm)).mp hxz
    have hpzy : polygonEventParameter P z ≤ polygonEventParameter P y := by
      apply le_of_not_gt
      intro h
      exact (not_lt_of_ge hzy)
        ((polygonEvent_sameEdge_lt_iff P hP.g2 y z (hye'.trans hze.symm)).mpr h)
    have hzinside := (eventPoint_mem_daughter_edge_iff P hP S root hroot i z hze).mpr
      ⟨hpz,lt_of_le_of_lt hpzy hparam.2⟩
    exact no_retained_event_in_daughter_edge P hP S root hroot i z hzret hze hzinside
  have hyx := dart_component_of_interval_no_retained P hP.g2 S x y hxy.le hno
  have hxr : componentOf (smoothingDartPermutation P hP.g2 S) x =
      componentOf (smoothingDartPermutation P hP.g2 S) root :=
    (orbitEnumeration (smoothingDartPermutation P hP.g2 S) root c.val).property
  exact hyx.trans hxr



end
end DirectGLSSW.DaughterInteriorComponent
