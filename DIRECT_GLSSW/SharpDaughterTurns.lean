import SharpDaughterCharacterization
import SharpDaughterTurnWellDefinedness
import PolygonPrincipalTurns

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.SharpDaughterRotation
open DirectGLSSW PermutationOrbits PrincipalTurning PolygonDrawingBridge SharpDaughter DaughterFirstReturn
open scoped BigOperators
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q))

def incomingTurn (y : PolygonEvent q) : ℝ :=
  Complex.arg (polygonEdgeVector q (polygonEventEdge q y) /
    polygonEdgeVector q (polygonEventEdge q ((P q hq S).symm y)))
def eventTurn (x : PolygonEvent q) : ℝ :=
  Complex.arg (polygonEdgeVector q (polygonEventEdge q (P q hq S x)) /
    polygonEdgeVector q (polygonEventEdge q x))

variable (C : Component (P q hq S))
    (hNA : PolygonNonalternation.polygonNonalternating q hq.g2 S)

theorem actual_arcVector (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    arcVector (sharpDaughterDiagram q hq S C hNA) a =
      arcVector (Parent q hq) (oldArc q hq S C a) := by
  simp only [arcVector, sharpDaughterDiagram, old_target, old_source]

theorem actual_turn (a : Fin (sharpDaughterDiagram q hq S C hNA).nArc) :
    turn (sharpDaughterDiagram q hq S C hNA) a =
      eventTurn q hq S (arcEquiv q hq S C a).val := by
  change Complex.arg (arcVector (sharpDaughterDiagram q hq S C hNA)
    (next q hq S C a) / arcVector (sharpDaughterDiagram q hq S C hNA) a) = _
  rw [actual_arcVector, actual_arcVector, old_next]
  change Complex.arg (arcVector (Parent q hq) (eventFin q (P q hq S (arcEquiv q hq S C a).val)) /
    arcVector (Parent q hq) (eventFin q (arcEquiv q hq S C a).val)) = _
  rw [polygonEvent_arcVector, polygonEvent_arcVector]
  exact turn_positive_rescale _ _ _ _ (PolygonDrawing.stepScale_pos q hq _)
    (PolygonDrawing.stepScale_pos q hq _)

theorem totalTurn_as_incoming :
    totalTurn (sharpDaughterDiagram q hq S C hNA) =
      ∑ a : Arc q hq S C, incomingTurn q hq S a.val := by
  calc
    totalTurn (sharpDaughterDiagram q hq S C hNA) =
        ∑ a : Arc q hq S C, eventTurn q hq S a.val :=
      Fintype.sum_equiv (arcEquiv q hq S C) _ _ (actual_turn q hq S C hNA)
    _ = ∑ a : Arc q hq S C, incomingTurn q hq S a.val := by
      apply Fintype.sum_equiv (fibrePerm (P q hq S) C)
      intro a
      simp only [eventTurn, incomingTurn, fibrePerm_apply_val, Equiv.symm_apply_apply]

omit C hNA in
theorem incomingTurn_noncorner (y : PolygonEvent q) (hy : ¬ retainedCorner q S y) :
    incomingTurn q hq S y = 0 := by
  have hfix := pairing_fixes_noncorner q S y hy
  have hp : P q hq S ((polygonEventSuccessor q hq.g2).symm y) = y := by
    rw [smoothingDartPermutation_apply, Equiv.apply_symm_apply, hfix]
  have hpred : (P q hq S).symm y = (polygonEventSuccessor q hq.g2).symm y := by
    have h := congrArg (P q hq S).symm hp
    simpa only [Equiv.symm_apply_apply] using h.symm
  rw [incomingTurn, hpred]
  have h := polygonEvent_turn_at_destination q hq y
  rw [polygonEvent_turn, Equiv.apply_symm_apply] at h
  cases y with
  | inl e => exact False.elim (hy trivial)
  | inr v => exact h

omit C hNA in
theorem sideComplex_positive_multiple (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
    (i : SharpDaughterTurning.CornerIndex q hq S root) :
    SharpDaughterTurning.sideComplex q hq S root i =
      Complex.ofReal (daughterSideScale q hq.g2 S root (cornerEnumeration q hq.g2 S root i)) *
        polygonEdgeVector q (polygonEventEdge q
          (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val)) := by
  apply Complex.equivRealProd.injective
  have h := (daughterSide_positive_multiple q hq.g2 S hq.size_ge_three root hroot i).2
  simpa only [SharpDaughterTurning.sideComplex, Complex.equivRealProd_apply,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    polygonEdgeVector, zero_mul, mul_zero, sub_zero, zero_add, add_zero,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk] using h

omit C hNA in
theorem cornerTurn_eq_carriers (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
    (i : SharpDaughterTurning.CornerIndex q hq S root) :
    SharpDaughterTurning.cornerTurn q hq S root hroot i =
      Complex.arg (polygonEdgeVector q (polygonEventEdge q
          (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val)) /
        polygonEdgeVector q (polygonEventEdge q
          (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root
            ((cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root))).symm i)).val))) := by
  unfold SharpDaughterTurning.cornerTurn
  rw [sideComplex_positive_multiple q hq S root hroot,
    sideComplex_positive_multiple q hq S root hroot]
  exact turn_positive_rescale _ _ _ _
    (daughterSide_positive_multiple q hq.g2 S hq.size_ge_three root hroot i).1
    (daughterSide_positive_multiple q hq.g2 S hq.size_ge_three root hroot _).1

omit C hNA in
theorem incomingTurn_at_corner (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
    (i : SharpDaughterTurning.CornerIndex q hq S root) :
    incomingTurn q hq S
      (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val) =
      SharpDaughterTurning.cornerTurn q hq S root hroot i := by
  let prev := (cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root))).symm i
  let cprev : CornerCoord q hq.g2 S root := cornerEnumeration q hq.g2 S root prev
  have hcyc : cyclicSuccessor prev = i :=
    (cyclicSuccessorPerm (Fintype.card (CornerCoord q hq.g2 S root))).apply_symm_apply i
  have hcornerNext : cornerSuccessor q hq.g2 S root cprev =
      cornerEnumeration q hq.g2 S root i := by
    rw [← cornerEnumeration_successor q hq.g2 S root prev]
    exact congrArg (cornerEnumeration q hq.g2 S root) hcyc
  have hnext := (cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hroot cprev).2.1
  change P q hq S (lastDartStart q hq.g2 S root cprev) =
    orbitEventAt q hq.g2 S root (cornerSuccessor q hq.g2 S root cprev).val at hnext
  rw [hcornerNext] at hnext
  have hpred : (P q hq S).symm
      (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val) =
      lastDartStart q hq.g2 S root cprev := by
    apply (P q hq S).injective
    rw [Equiv.apply_symm_apply, hnext]
  rw [cornerTurn_eq_carriers q hq S root hroot i, incomingTurn, hpred,
    ← DaughterTurns.daughterGapCarrierInvariant q hq.g2 S hq.size_ge_three root hroot cprev]

omit C in
theorem totalTurn_eq_cornerTotalTurn_root (root : PolygonEvent q)
    (hroot : retainedCorner q S root) :
    totalTurn (sharpDaughterDiagram q hq S (componentOf (P q hq S) root) hNA) =
      SharpDaughterTurning.cornerTotalTurn q hq S root hroot := by
  classical
  rw [totalTurn_as_incoming]
  calc
    (∑ a : Arc q hq S (componentOf (P q hq S) root), incomingTurn q hq S a.val) =
        ∑ j : OrbitCoord q hq.g2 S root,
          incomingTurn q hq S (orbitEventAt q hq.g2 S root j) :=
      (Fintype.sum_equiv (orbitEnumeration (P q hq S) root) _ _ (fun _ => rfl)).symm
    _ = ∑ c : CornerCoord q hq.g2 S root,
          incomingTurn q hq S (orbitEventAt q hq.g2 S root c.val) := by
      have hs := Fintype.sum_subtype_add_sum_subtype
        (fun j : OrbitCoord q hq.g2 S root => retainedCorner q S (orbitEventAt q hq.g2 S root j))
        (fun j => incomingTurn q hq S (orbitEventAt q hq.g2 S root j))
      have hz : (∑ j : {j : OrbitCoord q hq.g2 S root //
            ¬ retainedCorner q S (orbitEventAt q hq.g2 S root j)},
          incomingTurn q hq S (orbitEventAt q hq.g2 S root j.val)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact incomingTurn_noncorner q hq S _ j.property
      rw [hz, add_zero] at hs
      exact hs.symm
    _ = ∑ i : SharpDaughterTurning.CornerIndex q hq S root,
          incomingTurn q hq S
            (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val) :=
      (Fintype.sum_equiv (cornerEnumeration q hq.g2 S root).toEquiv _ _ (fun _ => rfl)).symm
    _ = SharpDaughterTurning.cornerTotalTurn q hq S root hroot := by
      apply Finset.sum_congr rfl
      intro i hi
      exact incomingTurn_at_corner q hq S root hroot i

theorem totalTurn_eq_cornerTotalTurn (root : PolygonEvent q)
    (hroot : retainedCorner q S root) (hC : componentOf (P q hq S) root = C) :
    totalTurn (sharpDaughterDiagram q hq S C hNA) =
      SharpDaughterTurning.cornerTotalTurn q hq S root hroot := by
  subst C
  exact totalTurn_eq_cornerTotalTurn_root q hq S hNA root hroot

end DirectGLSSW.HOMFLY.SharpDaughterRotation

