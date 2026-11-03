import DaughterPrefixParameters
import NoncornerOrbitGap

set_option autoImplicit false
namespace DirectGLSSW.DaughterEventCoverage
open DaughterFirstReturn DaughterOpenParameter DaughterPrefixParameters PermutationOrbits
noncomputable section

/-- Every omitted event of the root's actual orbit lies strictly inside its
preceding retained daughter's edge, on exactly the same original carrier. -/
theorem nonretained_event_in_daughter_edge {n : ℕ} (P : Fin n → PlanarPoint ℝ)
    (hP : CyclicGeneric P) (S : Finset (PolygonCrossing P))
    (root : PolygonEvent P) (hroot : retainedCorner P S root)
    (y : PolygonEvent P) (hy : ¬ retainedCorner P S y)
    (hcomp : componentOf (smoothingDartPermutation P hP.g2 S) y =
      componentOf (smoothingDartPermutation P hP.g2 S) root) :
    ∃ i : Fin (Fintype.card (CornerCoord P hP.g2 S root)),
      polygonEventEdge P y = daughterCarrier P hP.g2 S root i ∧
      edgeInterior (daughterVertex P hP.g2 S root) i (polygonEventPoint P y) := by
  classical
  let p := DartPerm P hP.g2 S
  let fy : Fibre p (componentOf p root) := ⟨y,hcomp⟩
  let r := (orbitEnumeration p root).symm fy
  have hry : orbitEventAt P hP.g2 S root r = y :=
    congrArg Subtype.val ((orbitEnumeration p root).apply_symm_apply fy)
  let C : OrbitCoord P hP.g2 S root → Prop := fun i =>
    retainedCorner P S (orbitEventAt P hP.g2 S root i)
  have hzero : C ⟨0,orbitCard_pos P hP.g2 S root⟩ := by
    simpa [C,orbitEventAt] using hroot
  have hr : ¬ C r := by simpa only [C,hry] using hy
  obtain ⟨c,k,hk0,hk,hreach⟩ := NoncornerOrbitGap.exists_preceding_retained
    (orbitCard_pos P hP.g2 S root) C hzero r hr
  have hkgap : k < cornerGap P hP.g2 S root c.val (cornerSuccessor P hP.g2 S root c).val := by
    simpa only [cornerGap,cornerSuccessor,FiniteFirstReturn.forwardGap] using hk
  have hiterate : (DartPerm P hP.g2 S ^ k) (orbitEventAt P hP.g2 S root c.val) = y := by
    rw [← orbitEventAt_iterate,hreach]
    exact hry
  let i := (cornerEnumeration P hP.g2 S root).symm c
  have hc : cornerEnumeration P hP.g2 S root i = c :=
    (cornerEnumeration P hP.g2 S root).apply_symm_apply c
  have he : polygonEventEdge P y = daughterCarrier P hP.g2 S root i := by
    change polygonEventEdge P y = polygonEventEdge P
      (orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val)
    rw [hc,← hiterate]
    exact (orbitPrefix_edge_parameter P hP.g2 S hP.size_ge_three root hroot c k hkgap).1
  refine ⟨i,he,(eventPoint_mem_daughter_edge_iff P hP S root hroot i y he).mpr ?_⟩
  rw [hc,← hiterate]
  exact orbitPrefix_parameter_bounds P hP.g2 S hP.size_ge_three root hroot c k hk0 hkgap


end
end DirectGLSSW.DaughterEventCoverage
