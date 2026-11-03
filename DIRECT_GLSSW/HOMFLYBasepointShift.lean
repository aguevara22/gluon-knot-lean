import DirectGLSSW.HOMFLY.HOMFLYAdjacentComponentSwapSupport

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

/-- Advance one component's chosen traversal root by its continuation successor. -/
noncomputable def advanceBaseTraversal {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) : BasedTraversal D := by
  classical
  refine ⟨T.componentIndex, ?_⟩
  intro C'
  by_cases h : C' = C
  · subst C'
    let b := T.baseArc C
    exact ⟨D.continuation b.val, by
      rw [PermutationOrbits.componentOf_apply]
      exact b.property⟩
  · exact T.baseArc C'

@[simp] theorem advanceBaseTraversal_componentIndex
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    (advanceBaseTraversal T C).componentIndex = T.componentIndex := rfl

theorem advanceBaseTraversal_baseArc_val
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    ((advanceBaseTraversal T C).baseArc C).val =
      D.continuation (T.baseArc C).val := by
  classical
  simp [advanceBaseTraversal]

private theorem orbitPosition_unique_from_power {D : PLLinkDiagram}
    (b : Fin D.nArc) {k l : ℕ}
    (hk : k < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation b)))
    (hl : l < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation b)))
    (hpow : (D.continuation ^ k) b = (D.continuation ^ l) b) :
    k = l := by
  let q := PermutationOrbits.orbitEnumeration D.continuation b
  have hq : q ⟨k, hk⟩ = q ⟨l, hl⟩ := by
    apply Subtype.ext
    simpa [q, PermutationOrbits.orbitEnumeration_apply_val] using hpow
  have hfin := q.injective hq
  exact congrArg Fin.val hfin

theorem visitPosition_advanceBase_nonroot
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (e : Fin D.nArc)
    (he : PermutationOrbits.componentOf D.continuation e = C)
    (hbase : e ≠ (T.baseArc C).val) :
    visitPosition (advanceBaseTraversal T C) e + 1 = visitPosition T e := by
  subst C
  let b := (T.baseArc (PermutationOrbits.componentOf D.continuation e)).val
  let k := visitPosition T e
  let j := visitPosition (advanceBaseTraversal T
    (PermutationOrbits.componentOf D.continuation e)) e
  let L := Fintype.card (PermutationOrbits.Fibre D.continuation
    (PermutationOrbits.componentOf D.continuation b))
  have hkbound : k < L := by
    dsimp [k, L, b]
    simpa using visitPosition_lt_orbitCard T e
  have hjbound : j < L := by
    dsimp [j, L, b]
    have hroot := advanceBaseTraversal_baseArc_val T
      (PermutationOrbits.componentOf D.continuation e)
    simpa [advanceBaseTraversal, hroot, PermutationOrbits.componentOf_apply] using
      visitPosition_lt_orbitCard
        (advanceBaseTraversal T (PermutationOrbits.componentOf D.continuation e)) e
  have hbase' : e ≠ b := by simpa [b] using hbase
  have hkpos : 0 < k := by
    dsimp [k]
    by_contra h
    have hk0 : visitPosition T e = 0 := by omega
    have hrec := visitPosition_reconstruct T e
    have heq : e = b := by simpa [hk0, b] using hrec.symm
    exact hbase' heq
  have hpowOld : (D.continuation ^ k) b = e := by
    simpa [k, b] using visitPosition_reconstruct T e
  have hpowCandidate : (D.continuation ^ (k - 1))
      (D.continuation b) = e := by
    calc
      (D.continuation ^ (k - 1)) (D.continuation b) =
          (D.continuation ^ (k - 1) * D.continuation) b := by
            rw [Equiv.Perm.mul_apply]
      _ = (D.continuation ^ ((k - 1) + 1)) b := by rw [← pow_succ]
      _ = (D.continuation ^ k) b := by rw [Nat.sub_add_cancel hkpos]
      _ = e := hpowOld
  have hpowNew : (D.continuation ^ j) (D.continuation b) = e := by
    simpa [j, b, advanceBaseTraversal_baseArc_val,
      PermutationOrbits.componentOf_apply] using
      visitPosition_reconstruct
        (advanceBaseTraversal T (PermutationOrbits.componentOf D.continuation e)) e
  have hboundCandidate : k - 1 < L := by omega
  have hboundCandidate' : k - 1 < Fintype.card
      (PermutationOrbits.Fibre D.continuation
        (PermutationOrbits.componentOf D.continuation (D.continuation b))) := by
    simpa [PermutationOrbits.componentOf_apply, L] using hboundCandidate
  have hunique := orbitPosition_unique_from_power (D.continuation b)
    (by simpa [PermutationOrbits.componentOf_apply] using hjbound)
    hboundCandidate' (hpowNew.trans hpowCandidate.symm)
  change j + 1 = k
  omega

theorem visitPosition_advanceBase_root
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) :
    visitPosition (advanceBaseTraversal T C) (T.baseArc C).val =
      Fintype.card (PermutationOrbits.Fibre D.continuation
        (PermutationOrbits.componentOf D.continuation (T.baseArc C).val)) - 1 := by
  let b := (T.baseArc C).val
  let j := visitPosition (advanceBaseTraversal T C) b
  let L := Fintype.card (PermutationOrbits.Fibre D.continuation
    (PermutationOrbits.componentOf D.continuation b))
  have hC : PermutationOrbits.componentOf D.continuation b = C :=
    (T.baseArc C).property
  have hbaseNew : ((advanceBaseTraversal T C).baseArc
      (PermutationOrbits.componentOf D.continuation b)).val = D.continuation b := by
    have hshift : advanceBaseTraversal T C =
        advanceBaseTraversal T (PermutationOrbits.componentOf D.continuation b) :=
      congrArg (advanceBaseTraversal T) hC.symm
    rw [hshift, advanceBaseTraversal_baseArc_val T
      (PermutationOrbits.componentOf D.continuation b)]
    have hv : (T.baseArc (PermutationOrbits.componentOf D.continuation b)).val = b := by
      have hh := congrArg (fun C => (T.baseArc C).val) hC
      simpa [b] using hh
    rw [hv]
  have hL : 0 < L := by
    dsimp [L]
    exact Fintype.card_pos_iff.mpr ⟨⟨b, rfl⟩⟩
  have hjbound : j < L := by
    dsimp [j, L]
    simpa [hbaseNew, PermutationOrbits.componentOf_apply] using
      visitPosition_lt_orbitCard (advanceBaseTraversal T C) b
  have hperiod : (D.continuation ^ L) b = b := by
    let last : Fin L := ⟨L - 1, by omega⟩
    have hsucc : DirectGLSSW.cyclicSuccessorPerm L last = 0 := by
      apply Fin.ext
      change (last.val + 1) % L = 0
      rw [show last.val = L - 1 by rfl]
      rw [Nat.sub_add_cancel hL, Nat.mod_self]
    have hstep := PermutationOrbits.orbitEnumeration_successor D.continuation b last
    rw [hsucc] at hstep
    have hv := congrArg Subtype.val hstep
    rw [PermutationOrbits.fibrePerm_apply_val,
      PermutationOrbits.orbitEnumeration_apply_val] at hv
    have hv' : b = D.continuation ((D.continuation ^ (L - 1)) b) := by
      simpa [last] using hv
    have hexp : (L - 1) + 1 = L := by omega
    calc
      (D.continuation ^ L) b =
          (D.continuation ^ ((L - 1) + 1)) b := by
            rw [hexp]
      _ = D.continuation ((D.continuation ^ (L - 1)) b) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
      _ = b := hv'.symm
  have hpowNew : (D.continuation ^ j) (D.continuation b) = b := by
    simpa [j, hbaseNew, PermutationOrbits.componentOf_apply] using
      visitPosition_reconstruct (advanceBaseTraversal T C) b
  have hpowLast : (D.continuation ^ (L - 1)) (D.continuation b) = b := by
    calc
      (D.continuation ^ (L - 1)) (D.continuation b) =
          (D.continuation ^ (L - 1) * D.continuation) b := by
            rw [Equiv.Perm.mul_apply]
      _ = (D.continuation ^ ((L - 1) + 1)) b := by rw [← pow_succ]
      _ = (D.continuation ^ L) b := by rw [Nat.sub_add_cancel (by omega)]
      _ = b := hperiod
  have hboundLast : L - 1 < L := by omega
  have hjbound' : j < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation (D.continuation b))) := by
    simpa [PermutationOrbits.componentOf_apply] using hjbound
  have hboundLast' : L - 1 < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation (D.continuation b))) := by
    simpa [PermutationOrbits.componentOf_apply, L] using hboundLast
  have hunique := orbitPosition_unique_from_power (D.continuation b) hjbound' hboundLast'
    (hpowNew.trans hpowLast.symm)
  change j = L - 1
  exact hunique


theorem visitPosition_advanceBase_other
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (e : Fin D.nArc)
    (he : PermutationOrbits.componentOf D.continuation e ≠ C) :
    visitPosition (advanceBaseTraversal T C) e = visitPosition T e := by
  classical
  let K := PermutationOrbits.componentOf D.continuation e
  let b := (T.baseArc K).val
  let k := visitPosition (advanceBaseTraversal T C) e
  let l := visitPosition T e
  have hb : (advanceBaseTraversal T C).baseArc K = T.baseArc K := by
    unfold advanceBaseTraversal
    simp [K, he]
  have hbv := congrArg Subtype.val hb
  have hcompShift : PermutationOrbits.componentOf D.continuation
      ((advanceBaseTraversal T C).baseArc K).val = K :=
    (advanceBaseTraversal T C).baseArc K |>.property
  have hcompOld : PermutationOrbits.componentOf D.continuation (T.baseArc K).val = K :=
    (T.baseArc K).property
  have hkbound : k < Fintype.card
      (PermutationOrbits.Fibre D.continuation K) := by
    have hh := visitPosition_lt_orbitCard (advanceBaseTraversal T C) e
    change k < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation
        ((advanceBaseTraversal T C).baseArc K).val)) at hh
    rw [hcompShift] at hh
    exact hh
  have hlbound : l < Fintype.card
      (PermutationOrbits.Fibre D.continuation K) := by
    have hh := visitPosition_lt_orbitCard T e
    change l < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation (T.baseArc K).val)) at hh
    rw [hcompOld] at hh
    exact hh
  have hk := visitPosition_reconstruct (advanceBaseTraversal T C) e
  have hl := visitPosition_reconstruct T e
  change (D.continuation ^ k) ((advanceBaseTraversal T C).baseArc K).val = e at hk
  change (D.continuation ^ l) (T.baseArc K).val = e at hl
  rw [hbv] at hk
  have hpow := hk.trans hl.symm
  have hkbound' : k < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation b)) := by
    simpa [b, hcompOld] using hkbound
  have hlbound' : l < Fintype.card (PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation b)) := by
    simpa [b, hcompOld] using hlbound
  have heq := orbitPosition_unique_from_power b hkbound' hlbound' hpow
  exact heq


private theorem if_fin2_eq_of_iff (p q : Prop) [Decidable p] [Decidable q]
    (hpq : p ↔ q) : (if p then (0 : Fin 2) else 1) = (if q then 0 else 1) := by
  by_cases hp : p
  · have hq : q := hpq.mp hp
    simp [hp, hq]
  · have hq : ¬ q := fun h => hp (hpq.mpr h)
    simp [hp, hq]

theorem firstVisitedBranch_advanceBase_of_mixed
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (c : Fin D.nCrossing)
    (hmix : PermutationOrbits.componentOf D.continuation (D.incoming c 0) ≠
      PermutationOrbits.componentOf D.continuation (D.incoming c 1)) :
    firstVisitedBranch (advanceBaseTraversal T C) c = firstVisitedBranch T c := by
  classical
  let e0 := D.incoming c 0
  let e1 := D.incoming c 1
  have hidx0 : (visitRank (advanceBaseTraversal T C) e0).1 = (visitRank T e0).1 := by
    simp [visitRank, advanceBaseTraversal]
  have hidx1 : (visitRank (advanceBaseTraversal T C) e1).1 = (visitRank T e1).1 := by
    simp [visitRank, advanceBaseTraversal]
  have hne : (visitRank T e0).1 ≠ (visitRank T e1).1 := by
    intro h
    exact hmix (T.componentIndex.injective h)
  unfold firstVisitedBranch
  apply if_fin2_eq_of_iff
  simp [rankBefore, visitRank, advanceBaseTraversal, hmix]


private theorem firstVisitedBranch_eq_of_same_component_shift
    {D : PLLinkDiagram} (T U : BasedTraversal D) (c : Fin D.nCrossing)
    (hcomp : PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
      PermutationOrbits.componentOf D.continuation (D.incoming c 1))
    (hpos0 : visitPosition U (D.incoming c 0) + 1 =
      visitPosition T (D.incoming c 0))
    (hpos1 : visitPosition U (D.incoming c 1) + 1 =
      visitPosition T (D.incoming c 1))
    (hidx : U.componentIndex = T.componentIndex) :
    firstVisitedBranch U c = firstVisitedBranch T c := by
  classical
  have hlt : visitPosition U (D.incoming c 0) < visitPosition U (D.incoming c 1) ↔
      visitPosition T (D.incoming c 0) < visitPosition T (D.incoming c 1) := by
    omega
  unfold firstVisitedBranch
  apply if_fin2_eq_of_iff
  simpa [rankBefore, visitRank, hidx, hcomp] using hlt



private theorem firstVisitedBranch_eq_of_same_component_order
    {D : PLLinkDiagram} (T U : BasedTraversal D) (c : Fin D.nCrossing)
    (hcomp : PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
      PermutationOrbits.componentOf D.continuation (D.incoming c 1))
    (hlt : visitPosition U (D.incoming c 0) < visitPosition U (D.incoming c 1) ↔
      visitPosition T (D.incoming c 0) < visitPosition T (D.incoming c 1))
    (hidx : U.componentIndex = T.componentIndex) :
    firstVisitedBranch U c = firstVisitedBranch T c := by
  classical
  unfold firstVisitedBranch
  apply if_fin2_eq_of_iff
  simpa [rankBefore, visitRank, hidx, hcomp] using hlt

theorem firstVisitedBranch_advanceBase_of_same_root_free
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (c : Fin D.nCrossing)
    (hcomp : PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
      PermutationOrbits.componentOf D.continuation (D.incoming c 1))
    (hroot0 : D.incoming c 0 ≠ (T.baseArc C).val)
    (hroot1 : D.incoming c 1 ≠ (T.baseArc C).val) :
    firstVisitedBranch (advanceBaseTraversal T C) c = firstVisitedBranch T c := by
  classical
  let e0 := D.incoming c 0
  let e1 := D.incoming c 1
  by_cases hC : PermutationOrbits.componentOf D.continuation e0 = C
  · have hC1 : PermutationOrbits.componentOf D.continuation e1 = C := hcomp.symm.trans hC
    have hp0 := visitPosition_advanceBase_nonroot T C e0 hC hroot0
    have hp1 := visitPosition_advanceBase_nonroot T C e1 hC1 hroot1
    exact firstVisitedBranch_eq_of_same_component_shift T (advanceBaseTraversal T C) c
      hcomp hp0 hp1 rfl
  · have hC1 : PermutationOrbits.componentOf D.continuation e1 ≠ C := by
      intro hh
      exact hC (hcomp.trans hh)
    have hp0 := visitPosition_advanceBase_other T C e0 hC
    have hp1 := visitPosition_advanceBase_other T C e1 hC1
    have hlt : visitPosition (advanceBaseTraversal T C) e0 <
        visitPosition (advanceBaseTraversal T C) e1 ↔
        visitPosition T e0 < visitPosition T e1 := by rw [hp0, hp1]
    exact firstVisitedBranch_eq_of_same_component_order T (advanceBaseTraversal T C) c
      hcomp (by simpa [e0, e1] using hlt) rfl


theorem branchChange_advanceBase_support
    {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (c : Fin D.nCrossing)
    (hchange : firstVisitedBranch (advanceBaseTraversal T C) c ≠ firstVisitedBranch T c) :
    (D.incoming c 0 = (T.baseArc C).val ∧
      PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
        PermutationOrbits.componentOf D.continuation (D.incoming c 1)) ∨
    (D.incoming c 1 = (T.baseArc C).val ∧
      PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
        PermutationOrbits.componentOf D.continuation (D.incoming c 1)) := by
  classical
  by_cases hcomp : PermutationOrbits.componentOf D.continuation (D.incoming c 0) =
      PermutationOrbits.componentOf D.continuation (D.incoming c 1)
  · by_cases hroot0 : D.incoming c 0 = (T.baseArc C).val
    · exact Or.inl ⟨hroot0, hcomp⟩
    · by_cases hroot1 : D.incoming c 1 = (T.baseArc C).val
      · exact Or.inr ⟨hroot1, hcomp⟩
      · have heq := firstVisitedBranch_advanceBase_of_same_root_free T C c hcomp hroot0 hroot1
        exact False.elim (hchange heq)
  · have heq := firstVisitedBranch_advanceBase_of_mixed T C c hcomp
    exact False.elim (hchange heq)

end DirectGLSSW.HOMFLY
