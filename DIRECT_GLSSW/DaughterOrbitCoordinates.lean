import FiniteRetainedPrefix
import DaughterLocalCrossingEquiv

set_option autoImplicit false
namespace DirectGLSSW.DaughterOrbitCoordinates
open DaughterFirstReturn DaughterPrefixParameters PolygonNonalternation
noncomputable section

variable {n : ℕ} (P : Fin n → PlanarPoint ℝ) (hP : CyclicGeneric P)
variable (S : Finset (PolygonCrossing P)) (hS : polygonNonalternating P hP.g2 S)
variable (root : PolygonEvent P) (hroot : retainedCorner P S root)
include hS hroot

/-- The actual orbit coordinate on a daughter carrier is a unique linear prefix
of that daughter's retained start; no wrap is hidden in the displayed sum. -/
theorem orbitCoordinate_prefix (r : OrbitCoord P hP.g2 S root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (he : polygonEventEdge P (orbitEventAt P hP.g2 S root r) = daughterCarrier P hP.g2 S root i) :
    ∃ k : ℕ,
      k < cornerGap P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val
        (cornerSuccessor P hP.g2 S root (cornerEnumeration P hP.g2 S root i)).val ∧
      r.val = (cornerEnumeration P hP.g2 S root i).val.val+k ∧
      orbitEventAt P hP.g2 S root r =
        (DartPerm P hP.g2 S ^ k)
          (orbitEventAt P hP.g2 S root (cornerEnumeration P hP.g2 S root i).val) := by
  classical
  let C : OrbitCoord P hP.g2 S root → Prop := fun r =>
    retainedCorner P S (orbitEventAt P hP.g2 S root r)
  have hzero : C ⟨0,orbitCard_pos P hP.g2 S root⟩ := by
    simpa [C,orbitEventAt] using hroot
  obtain ⟨c,k,hk,hreach,hrval,_⟩ := FiniteRetainedPrefix.exists_prefix
    (orbitCard_pos P hP.g2 S root) C hzero r
  have hkgap : k < cornerGap P hP.g2 S root c.val (cornerSuccessor P hP.g2 S root c).val := by
    simpa only [cornerGap,cornerSuccessor,FiniteFirstReturn.forwardGap] using hk
  have hiter : orbitEventAt P hP.g2 S root r =
      (DartPerm P hP.g2 S ^ k) (orbitEventAt P hP.g2 S root c.val) := by
    rw [← hreach,orbitEventAt_iterate]
  let j := (cornerEnumeration P hP.g2 S root).symm c
  have hc : cornerEnumeration P hP.g2 S root j = c :=
    (cornerEnumeration P hP.g2 S root).apply_symm_apply c
  have hji : j = i := by
    apply daughterCarrier_injective P hP.g2 S hP.size_ge_three hS root
    change polygonEventEdge P (orbitEventAt P hP.g2 S root
      (cornerEnumeration P hP.g2 S root j).val) = daughterCarrier P hP.g2 S root i
    rw [hc]
    have hprefix := (orbitPrefix_edge_parameter P hP.g2 S hP.size_ge_three root hroot c k hkgap).1
    exact hprefix.symm.trans (hiter ▸ he)
  have hci : c = cornerEnumeration P hP.g2 S root i := hc.symm.trans (congrArg _ hji)
  rw [hci] at hkgap hrval hiter
  exact ⟨k,hkgap,hrval,hiter⟩

/-- A carrier block starts at its retained coordinate and is below every later
retained coordinate, including the immediate next corner whenever nonterminal. -/
theorem orbitCoordinate_bounds (r : OrbitCoord P hP.g2 S root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (he : polygonEventEdge P (orbitEventAt P hP.g2 S root r) = daughterCarrier P hP.g2 S root i) :
    (cornerEnumeration P hP.g2 S root i).val.val ≤ r.val ∧
      ∀ j, i < j → r.val < (cornerEnumeration P hP.g2 S root j).val.val := by
  classical
  obtain ⟨k,hk,hr,_⟩ := orbitCoordinate_prefix P hP S hS root hroot r i he
  let C : OrbitCoord P hP.g2 S root → Prop := fun r =>
    retainedCorner P S (orbitEventAt P hP.g2 S root r)
  have hzero : C ⟨0,orbitCard_pos P hP.g2 S root⟩ := by
    simpa [C,orbitEventAt] using hroot
  have hkgap : k < FiniteFirstReturn.forwardGap (cornerEnumeration P hP.g2 S root i).val
      (orderedCyclicSuccessor (CornerCoord P hP.g2 S root) (cornerEnumeration P hP.g2 S root i)).val := by
    simpa only [cornerGap,cornerSuccessor,FiniteFirstReturn.forwardGap] using hk
  have hb := (FiniteRetainedPrefix.prefix_no_wrap (orbitCard_pos P hP.g2 S root)
    C hzero (cornerEnumeration P hP.g2 S root i) k hkgap).2
  refine ⟨by omega,?_⟩
  intro j hij
  rw [hr]
  exact hb _ ((cornerEnumeration P hP.g2 S root).strictMono hij)

theorem orbitCoordinate_lt_of_carrier_lt (r s : OrbitCoord P hP.g2 S root)
    (i j : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (her : polygonEventEdge P (orbitEventAt P hP.g2 S root r) = daughterCarrier P hP.g2 S root i)
    (hes : polygonEventEdge P (orbitEventAt P hP.g2 S root s) = daughterCarrier P hP.g2 S root j)
    (hij : i < j) : r < s := by
  exact ((orbitCoordinate_bounds P hP S hS root hroot r i her).2 j hij).trans_le
    (orbitCoordinate_bounds P hP S hS root hroot s j hes).1

/-- On one actual carrier block, orbit order is exactly original edge-parameter order. -/
theorem orbitCoordinate_lt_iff_parameter_lt (r s : OrbitCoord P hP.g2 S root)
    (i : Fin (Fintype.card (CornerCoord P hP.g2 S root)))
    (her : polygonEventEdge P (orbitEventAt P hP.g2 S root r) = daughterCarrier P hP.g2 S root i)
    (hes : polygonEventEdge P (orbitEventAt P hP.g2 S root s) = daughterCarrier P hP.g2 S root i) :
    r < s ↔ polygonEventParameter P (orbitEventAt P hP.g2 S root r) <
      polygonEventParameter P (orbitEventAt P hP.g2 S root s) := by
  obtain ⟨k,hk,hr,her'⟩ := orbitCoordinate_prefix P hP S hS root hroot r i her
  obtain ⟨l,hl,hs,hes'⟩ := orbitCoordinate_prefix P hP S hS root hroot s i hes
  rw [her',hes']
  constructor
  · intro hrs
    have hkl : k < l := by change r.val < s.val at hrs; omega
    have hstep := orbitPrefix_parameter_step P hP.g2 S hP.size_ge_three root hroot
      (cornerEnumeration P hP.g2 S root i) k (by omega)
    have hmono := orbitPrefix_parameter_mono P hP.g2 S hP.size_ge_three root hroot
      (cornerEnumeration P hP.g2 S root i) (k+1) l (by omega) hl
    exact hstep.trans_le hmono
  · intro hparam
    apply lt_of_not_ge
    intro hsr
    have hlk : l ≤ k := by change s.val ≤ r.val at hsr; omega
    exact (not_lt_of_ge (orbitPrefix_parameter_mono P hP.g2 S hP.size_ge_three root hroot
      (cornerEnumeration P hP.g2 S root i) l k hlk hk)) hparam





end
end DirectGLSSW.DaughterOrbitCoordinates
