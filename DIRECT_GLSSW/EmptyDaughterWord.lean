import DirectGLSSW.RealPolygons
import DirectGLSSW.DaughterPointListFilter
import DirectGLSSW.OrbitWordPrerequisite

set_option autoImplicit false
namespace DirectGLSSW.EmptyDaughterWord
open DaughterFirstReturn PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem empty_daughterPointList_zero {n : ℕ} (hn : 0 < n)
    (P : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections P) :
    daughterPointList P hG2 ∅ (Sum.inl (⟨0,hn⟩ : Fin n)) = List.ofFn P := by
  letI : LinearOrder (PolygonEvent P) := polygonEventOrder P hG2
  letI : LinearOrder (Fin n ⊕ CrossingVisit P) := polygonEventOrder P hG2
  let E := increasingEnumeration (PolygonEvent P)
  let z : PolygonEvent P := Sum.inl (⟨0,hn⟩ : Fin n)
  have hN : 0 < Fintype.card (PolygonEvent P) := Fintype.card_pos_iff.mpr ⟨z⟩
  have hzmin (y : PolygonEvent P) : z ≤ y := by
    apply le_of_not_gt
    intro hlt
    rcases (polygonEvent_lt_iff P hG2 y z).mp hlt with h | ⟨_,h⟩
    · change (polygonEventEdge P y).val < 0 at h
      omega
    · exact (not_lt_of_ge (polygonEventParameter_bounds P y).1) h
  have hemin (y : PolygonEvent P) : E ⟨0,hN⟩ ≤ y := by
    rw [← E.apply_symm_apply y]
    exact E.monotone (show (⟨0,hN⟩ : Fin (Fintype.card (PolygonEvent P))) ≤ E.symm y from Nat.zero_le _)
  have hE0 : E (⟨0,hN⟩ : Fin (Fintype.card (PolygonEvent P))) = z :=
    le_antisymm (hemin z) (hzmin _)
  have hstep (i : Fin (Fintype.card (PolygonEvent P))) :
      polygonEventSuccessor P hG2 (E i) = E (cyclicSuccessor i) := by
    change orderedCyclicSuccessor (PolygonEvent P) (E i) = E (cyclicSuccessor i)
    simp only [orderedCyclicSuccessor_apply,E,OrderIso.symm_apply_apply]
  have hw := orbitWord_eq_of_injective_cyclicSuccessor (polygonEventSuccessor P hG2)
    hN E E.injective hstep
  rw [hE0] at hw
  have ha : List.ofFn (fun i : Fin n => (Sum.inl i : PolygonEvent P)) =
      (List.ofFn E).filter (fun y => decide (retainedCorner P ∅ y)) := by
    have hs1 : (List.ofFn (fun i : Fin n => (Sum.inl i : PolygonEvent P))).Sorted (· < ·) := by
      apply List.sorted_lt_ofFn_iff.mpr
      intro i j hij
      exact (polygonEvent_anchor_lt_iff P hG2 i j).mpr hij
    have hs2 : ((List.ofFn E).filter (fun y => decide (retainedCorner P ∅ y))).Sorted (· < ·) :=
      (List.sorted_lt_ofFn_iff.mpr E.strictMono).filter _
    apply List.Sorted.eq_of_mem_iff hs1 hs2
    intro y
    cases y with
    | inl i =>
      constructor
      · intro _
        exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨E.symm (Sum.inl i),E.apply_symm_apply _⟩,by simp [retainedCorner]⟩
      · intro _
        exact List.mem_ofFn.mpr ⟨i,rfl⟩
    | inr v => simp [retainedCorner,List.mem_ofFn]
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,
    smoothingDartPermutation_empty]
  change ((orbitWord (polygonEventSuccessor P hG2) z).filter _).map _ = _
  rw [hw,← ha,List.map_ofFn]
  rfl


end
end DirectGLSSW.EmptyDaughterWord
