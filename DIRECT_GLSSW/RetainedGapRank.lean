import DirectGLSSW.DaughterFirstReturn
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DaughterFirstReturn
open Equiv PermutationOrbits
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (q : Fin n → PlanarPoint K) (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)

/-- The last retained gap ends at rooted coordinate zero; all gaps therefore
fit before the numerical end of the actual orbit. -/
theorem cornerGap_le_remaining (hroot : retainedCorner q S root)
    (c : CornerCoord q hG2 S root) :
    cornerGap q hG2 S root c.val (cornerSuccessor q hG2 S root c).val ≤
      orbitCard q hG2 S root-c.val.val := by
  classical
  let z : CornerCoord q hG2 S root:=⟨⟨0,orbitCard_pos q hG2 S root⟩,by simpa [orbitEventAt] using hroot⟩
  have hs:=orderedCyclicSuccessor_order_spec (CornerCoord q hG2 S root) c
  change (c<cornerSuccessor q hG2 S root c ∧ _) ∨ _ at hs
  rcases hs with ⟨hinc,_⟩ | ⟨_,hmin⟩
  · have hi : c.val.val < (cornerSuccessor q hG2 S root c).val.val:=hinc
    have hn:=(cornerSuccessor q hG2 S root c).val.isLt
    unfold cornerGap
    rw [if_pos hi]
    omega
  · have hz:=hmin z
    change (cornerSuccessor q hG2 S root c).val.val≤0 at hz
    have hn:=c.val.isLt
    unfold cornerGap
    split_ifs <;> omega

/-- An actual finite dart iterate in the root's continuation fibre. -/
def cornerGap_offset_fibre (c : CornerCoord q hG2 S root) (k : ℕ) :
    Fibre (DartPerm q hG2 S) (componentOf (DartPerm q hG2 S) root) :=
  ⟨(DartPerm q hG2 S ^ k) (orbitEventAt q hG2 S root c.val),by
    rw [componentOf_pow_apply]
    exact (orbitEnumeration (DartPerm q hG2 S) root c.val).property⟩

/-- Strict gap offsets do not wrap, even in the final gap. The inverse actual
orbit enumeration has the literal natural coordinate c+k. -/
theorem cornerGap_offset_rank (hroot : retainedCorner q S root)
    (c : CornerCoord q hG2 S root) (k : ℕ)
    (hk : k < cornerGap q hG2 S root c.val (cornerSuccessor q hG2 S root c).val) :
    c.val.val+k < orbitCard q hG2 S root ∧
    ((orbitEnumeration (DartPerm q hG2 S) root).symm
      (cornerGap_offset_fibre q hG2 S root c k)).val=c.val.val+k := by
  have hle:=cornerGap_le_remaining q hG2 S root hroot c
  have hc:=c.val.isLt
  have hbound:c.val.val+k<orbitCard q hG2 S root:=by omega
  refine ⟨hbound,?_⟩
  have he : orbitEnumeration (DartPerm q hG2 S) root
      ((cyclicSuccessorPerm (orbitCard q hG2 S root)^k) c.val)=
        cornerGap_offset_fibre q hG2 S root c k := by
    apply Subtype.ext
    exact orbitEventAt_iterate q hG2 S root c.val k
  rw [←he,Equiv.symm_apply_apply]
  rw [FiniteFirstReturn.cyclicSuccessorPerm_pow_val_of_lt c.val (by omega),if_pos hbound]
end DirectGLSSW.DaughterFirstReturn
