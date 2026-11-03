import DirectGLSSW.DaughterFirstReturn
import MarkedCyclePartition
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterFirstReturn
open Equiv PermutationOrbits MarkedCycleGaps
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (q : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)

/-- The two existing first-return constructions have exactly the same length. -/
theorem cornerGap_eq_markedGap (c : CornerCoord q hG2 S root) :
    cornerGap q hG2 S root c.val (cornerSuccessor q hG2 S root c).val =
      gapLength (cyclicSuccessorPerm (orbitCard q hG2 S root))
        (fun j : CornerCoord q hG2 S root => j.val) c := by
  let P : OrbitCoord q hG2 S root → Prop :=
    fun i => retainedCorner q S (orbitEventAt q hG2 S root i)
  obtain ⟨hpos,hle,hreach,hno⟩ := FiniteFirstReturn.orderedSubtype_firstReturn P c
  apply (gapLength_characterization _ _ _ _).mpr
  refine ⟨hpos,⟨cornerSuccessor q hG2 S root c,hreach⟩,?_⟩
  intro k hk hkd he
  obtain ⟨j,hj⟩ := he
  apply hno k hk hkd
  rw [hj]
  exact j.property

/-- Every nonretained event of the actual dart orbit lies strictly inside a
retained first-return gap. No assumed gap partition or geometric hypothesis. -/
theorem nonretained_event_in_cornerGap
    (hroot : retainedCorner q S root) (x : PolygonEvent q)
    (hx : componentOf (DartPerm q hG2 S) x = componentOf (DartPerm q hG2 S) root)
    (hnot : ¬ retainedCorner q S x) :
    ∃ i : Fin (Fintype.card (CornerCoord q hG2 S root)), ∃ k : ℕ,
      0 < k ∧
      k < cornerGap q hG2 S root (cornerEnumeration q hG2 S root i).val
        (cornerSuccessor q hG2 S root (cornerEnumeration q hG2 S root i)).val ∧
      x = (DartPerm q hG2 S ^ k)
        (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) := by
  let p := cyclicSuccessorPerm (orbitCard q hG2 S root)
  let mark : CornerCoord q hG2 S root → OrbitCoord q hG2 S root := Subtype.val
  letI : Nonempty (CornerCoord q hG2 S root) :=
    ⟨⟨⟨0,orbitCard_pos q hG2 S root⟩,by simpa [orbitEventAt] using hroot⟩⟩
  have hp : p.IsCycleOn Set.univ := by
    refine ⟨p.bijOn (fun _ => Iff.rfl),?_⟩
    intro a _ b _
    refine ⟨(FiniteFirstReturn.forwardGap a b : ℤ),?_⟩
    rw [zpow_natCast]
    exact FiniteFirstReturn.cyclicSuccessor_pow_forwardGap a b
  let ix := (orbitEnumeration (DartPerm q hG2 S) root).symm ⟨x,hx⟩
  have hix : orbitEventAt q hG2 S root ix = x :=
    congrArg Subtype.val ((orbitEnumeration (DartPerm q hG2 S) root).apply_symm_apply ⟨x,hx⟩)
  obtain ⟨⟨c,k⟩,hk⟩ := gapMap_surjective p mark hp ix
  change (p ^ (k.val+1)) c.val = ix at hk
  have hle : k.val+1 ≤ gapLength p mark c := by omega
  have hne : k.val+1 ≠ gapLength p mark c := by
    intro heq
    obtain ⟨j,hj⟩ := gapLength_return p mark c
    rw [← heq,hk] at hj
    apply hnot
    rw [← hix,hj]
    exact j.property
  have hlt : k.val+1 < gapLength p mark c := lt_of_le_of_ne hle hne
  refine ⟨(cornerEnumeration q hG2 S root).symm c,k.val+1,by omega,?_,?_⟩
  · simpa only [OrderIso.apply_symm_apply,cornerGap_eq_markedGap] using hlt
  · rw [OrderIso.apply_symm_apply]
    calc
      x = orbitEventAt q hG2 S root ix := hix.symm
      _ = orbitEventAt q hG2 S root ((p ^ (k.val+1)) c.val) := congrArg _ hk.symm
      _ = _ := orbitEventAt_iterate q hG2 S root c.val (k.val+1)



end DirectGLSSW.DaughterFirstReturn
