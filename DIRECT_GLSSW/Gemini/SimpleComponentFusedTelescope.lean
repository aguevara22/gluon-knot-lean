import Gemini.SelfCrossingLoopDeletion

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY.Gemini

open DirectGLSSW.HOMFLY DirectGLSSW.HOMFLY.Coefficients
open Equiv PermutationOrbits

noncomputable section
attribute [local instance] Classical.propDecidable
local instance (D : PLLinkDiagram) : DecidableEq (diagramComponent D) := Classical.decEq _
local instance (D : PLLinkDiagram) : Fintype (diagramComponent D) :=
  PermutationOrbits.componentFintype D.continuation

/-! ### Part 1: Join Component Count and Unlink Factor Identities -/

theorem smooth_componentCount_join (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hjoin : ¬ D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1)) :
    diagramComponentCount (smoothCrossing D c) + 1 = diagramComponentCount D := by
  have h1 : diagramComponentCount (smoothCrossing D c) = componentCount (cutContinuation D c) :=
    (Fintype.card_congr (smoothCutComponentEquiv D c)).symm
  rw [h1]
  exact componentCount_mul_swap_of_not_sameCycle D.continuation hjoin

theorem descendingUnlinkValue_smooth_join (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (hjoin : ¬ D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1))
    (hge2 : 2 ≤ diagramComponentCount D) :
    descendingUnlinkValue (smoothCrossing D c) =
      unlinkFactor ^ (diagramComponentCount D - 2) := by
  have hJoinCount := smooth_componentCount_join D c hjoin
  have hsmooth : 0 < diagramComponentCount (smoothCrossing D c) := by omega
  rw [descendingUnlinkValue_of_nonempty_components (smoothCrossing D c) hsmooth]
  have hexp : diagramComponentCount (smoothCrossing D c) - 1 = diagramComponentCount D - 2 := by
    omega
  rw [hexp]

theorem descendingUnlinkValue_eq_mul_pow_sub_two (D : PLLinkDiagram)
    (hge2 : 2 ≤ diagramComponentCount D) :
    descendingUnlinkValue D =
      unlinkFactor * unlinkFactor ^ (diagramComponentCount D - 2) := by
  have hD : 0 < diagramComponentCount D := by omega
  rw [descendingUnlinkValue_of_nonempty_components D hD]
  have hexp : diagramComponentCount D - 1 = (diagramComponentCount D - 2) + 1 := by omega
  rw [hexp, pow_succ']

theorem pivot_unlink_factor_identity (D : PLLinkDiagram) (c : Fin D.nCrossing) :
    pivotSwitchFactor D c + pivotSmoothFactor D c * unlinkFactor = 1 := by
  have hai : aInvMonomial * aMonomial = 1 := by
    rw [mul_comm, aMonomial_mul_aInvMonomial]
  have hzi : zMonomial * zInvMonomial = 1 := zMonomial_mul_zInvMonomial
  rw [pivotSwitchFactor, pivotSmoothFactor, unlinkFactor]
  rcases crossingSign D c with _ | _ <;> dsimp only
  · calc
      aMonomial * aMonomial +
          -(aMonomial * zMonomial) * ((aMonomial - aInvMonomial) * zInvMonomial) =
        (aMonomial * aInvMonomial) * (zMonomial * zInvMonomial) +
          aMonomial * aMonomial * (1 - zMonomial * zInvMonomial) := by ring
      _ = 1 := by rw [aMonomial_mul_aInvMonomial, hzi]; ring
  · calc
      aInvMonomial * aInvMonomial +
          aInvMonomial * zMonomial * ((aMonomial - aInvMonomial) * zInvMonomial) =
        (aInvMonomial * aMonomial) * (zMonomial * zInvMonomial) +
          aInvMonomial * aInvMonomial * (1 - zMonomial * zInvMonomial) := by ring
      _ = 1 := by rw [hai, hzi]; ring

theorem skein_step_telescope_identity (D : PLLinkDiagram) (c : Fin D.nCrossing)
    (V V_sw Q : HOMFLYCoeff)
    (hskein : V = pivotSwitchFactor D c * V_sw + pivotSmoothFactor D c * Q) :
    unlinkFactor * V - Q =
      pivotSwitchFactor D c * (unlinkFactor * V_sw - Q) := by
  rw [hskein]
  calc
    unlinkFactor * (pivotSwitchFactor D c * V_sw + pivotSmoothFactor D c * Q) - Q =
        unlinkFactor * (pivotSwitchFactor D c * V_sw + pivotSmoothFactor D c * Q) -
          1 * Q := by ring
    _ = unlinkFactor * (pivotSwitchFactor D c * V_sw + pivotSmoothFactor D c * Q) -
          (pivotSwitchFactor D c + pivotSmoothFactor D c * unlinkFactor) * Q := by
          rw [pivot_unlink_factor_identity D c]
    _ = pivotSwitchFactor D c * (unlinkFactor * V_sw - Q) := by ring

/-! ### Part 2: Mixed Crossings and Simple Component Predicates -/

def HasNoSelfCrossings (D : PLLinkDiagram) (A : diagramComponent D) : Prop :=
  ∀ c : Fin D.nCrossing,
    (componentOf D.continuation (D.incoming c 0) : diagramComponent D) = A →
    (componentOf D.continuation (D.incoming c 1) : diagramComponent D) ≠ A

theorem swap_01_eq_otherBranch (j : Fin 2) :
    Equiv.swap (0 : Fin 2) 1 j = otherBranch j := by
  fin_cases j <;> rfl

theorem eq_otherBranch_of_ne (j k : Fin 2) (h : j ≠ k) :
    j = otherBranch k := by
  fin_cases j <;> fin_cases k <;> first | exact False.elim (h rfl) | rfl

theorem firstVisitedBranch_reindex_adjacent_of_affected
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    firstVisitedBranch (reindexTraversalComponents T (adjacentComponentSwap r hr)) c =
      otherBranch (firstVisitedBranch T c) := by
  rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [firstVisitedBranch_reindex_adjacent_components_of_mixed T r hr c h0 h1,
      swap_01_eq_otherBranch]
  · rw [firstVisitedBranch_reindex_adjacent_components_of_mixed_reverse T r hr c h0 h1,
      swap_01_eq_otherBranch]

theorem affected_firstVisitedBranch_T_eq_zero_of_left
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (h0 : T.componentIndex (componentOf D.continuation (D.incoming c 0)) = r)
    (h1 : (T.componentIndex (componentOf D.continuation (D.incoming c 1))).val = r.val + 1) :
    firstVisitedBranch T c = 0 := by
  unfold firstVisitedBranch
  have hrb : rankBefore (visitRank T (D.incoming c 0)) (visitRank T (D.incoming c 1)) := by
    left
    dsimp [visitRank]
    rw [Fin.lt_iff_val_lt_val, h0, h1]
    omega
  rw [if_pos hrb]

theorem affected_firstVisitedBranch_T_eq_one_of_right
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (h0 : (T.componentIndex (componentOf D.continuation (D.incoming c 0))).val = r.val + 1)
    (h1 : T.componentIndex (componentOf D.continuation (D.incoming c 1)) = r) :
    firstVisitedBranch T c = 1 := by
  unfold firstVisitedBranch
  have hnrb : ¬ rankBefore (visitRank T (D.incoming c 0)) (visitRank T (D.incoming c 1)) := by
    rintro (hlt | ⟨hEq, _⟩)
    · rw [Fin.lt_iff_val_lt_val] at hlt
      dsimp [visitRank] at hlt
      rw [h0, h1] at hlt
      omega
    · dsimp [visitRank] at hEq
      have hv := congrArg Fin.val hEq
      rw [h0, h1] at hv
      omega
  rw [if_neg hnrb]

theorem affected_branch_A_componentIndex
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (hc : adjacentSwapAffectedCrossing T r c) :
    T.componentIndex (componentOf D.continuation (D.incoming c (firstVisitedBranch T c))) = r := by
  rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [affected_firstVisitedBranch_T_eq_zero_of_left T r c h0 h1]
    exact h0
  · rw [affected_firstVisitedBranch_T_eq_one_of_right T r c h0 h1]
    exact h1

theorem affected_branch_B_componentIndex_val
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (hc : adjacentSwapAffectedCrossing T r c) :
    (T.componentIndex (componentOf D.continuation
      (D.incoming c (otherBranch (firstVisitedBranch T c))))).val = r.val + 1 := by
  rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [affected_firstVisitedBranch_T_eq_zero_of_left T r c h0 h1]
    exact h1
  · rw [affected_firstVisitedBranch_T_eq_one_of_right T r c h0 h1]
    exact h0

theorem affected_branch_B_componentOf
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    componentOf D.continuation (D.incoming c (otherBranch (firstVisitedBranch T c))) =
      T.componentIndex.symm ⟨r.val + 1, hr⟩ := by
  apply T.componentIndex.injective
  apply Fin.ext
  rw [affected_branch_B_componentIndex_val T r c hc]
  exact (congrArg Fin.val (T.componentIndex.apply_symm_apply ⟨r.val + 1, hr⟩)).symm

theorem affected_kB_lt_LB
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) <
      Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩)) := by
  have h := visitPosition_lt_card T (D.incoming c (otherBranch (firstVisitedBranch T c)))
  rwa [affected_branch_B_componentOf T r hr c hc] at h

theorem affected_not_sameCycle
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (hc : adjacentSwapAffectedCrossing T r c) :
    ¬ D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1) := by
  intro hsc
  have hcomp : componentOf D.continuation (D.incoming c 0) =
      componentOf D.continuation (D.incoming c 1) :=
    (componentOf_eq_iff _ _ _).mpr hsc
  have hidx : (T.componentIndex (componentOf D.continuation (D.incoming c 0))).val =
      (T.componentIndex (componentOf D.continuation (D.incoming c 1))).val :=
    congrArg (fun C => (T.componentIndex C).val) hcomp
  rcases hc with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1] at hidx; omega
  · rw [h0, h1] at hidx; omega

/-! ### Part 3: Merged Orbit Powers Under Mixed Smoothing -/

theorem cutContinuation_incoming_eq (D : PLLinkDiagram) (c : Fin D.nCrossing) (j : Fin 2) :
    cutContinuation D c (D.incoming c j) =
      D.continuation (D.incoming c (otherBranch j)) := by
  unfold cutContinuation
  fin_cases j
  · dsimp [otherBranch]
    rw [Equiv.swap_apply_left]
  · dsimp [otherBranch]
    rw [Equiv.swap_apply_right]

theorem smooth_step_incoming (D : PLLinkDiagram) (c : Fin D.nCrossing) (j : Fin 2) :
    (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl (D.incoming c j))) =
      smoothArcEquiv D (Sum.inr j) := by
  rw [← smoothCode_actual_step D c (Sum.inl (D.incoming c j)),
    smoothCode_cut_step D c j]

theorem smooth_step_connector (D : PLLinkDiagram) (c : Fin D.nCrossing) (j : Fin 2) :
    (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inr j)) =
      smoothArcEquiv D (Sum.inl (D.continuation (D.incoming c (otherBranch j)))) := by
  rw [← smoothCode_actual_step D c (Sum.inr j),
    smoothCode_new_step D c j, cutContinuation_incoming_eq D c j]

theorem pow_rootB_ne_incoming_of_ne_kB
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (u : ℕ)
    (hu : u < Fintype.card (Fibre D.continuation
      (T.componentIndex.symm ⟨r.val + 1, hr⟩)))
    (hne : u ≠ visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))))
    (j : Fin 2) :
    (D.continuation ^ u) (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val ≠
      D.incoming c j := by
  let B := T.componentIndex.symm ⟨r.val + 1, hr⟩
  let rootB := (T.baseArc B).val
  have hrootB_comp : componentOf D.continuation rootB = B := (T.baseArc B).property
  have hu_comp : componentOf D.continuation ((D.continuation ^ u) rootB) = B := by
    rw [componentOf_pow_apply, hrootB_comp]
  have hB_idx : (T.componentIndex B).val = r.val + 1 := by
    dsimp [B]
    rw [T.componentIndex.apply_symm_apply]
  intro hEq
  by_cases hj : j = firstVisitedBranch T c
  · subst hj
    have hj_idx := affected_branch_A_componentIndex T r c hc
    have hEq_idx : (T.componentIndex (componentOf D.continuation ((D.continuation ^ u) rootB))).val =
        (T.componentIndex (componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))).val :=
      congrArg (fun a => (T.componentIndex (componentOf D.continuation a)).val) hEq
    rw [hu_comp, hB_idx, hj_idx] at hEq_idx
    omega
  · have hj_other : j = otherBranch (firstVisitedBranch T c) :=
      eq_otherBranch_of_ne j (firstVisitedBranch T c) hj
    subst hj_other
    have hbase : (T.baseArc (componentOf D.continuation rootB)).val = rootB := by
      rw [hrootB_comp]
    have hu_lt : u < Fintype.card (Fibre D.continuation (componentOf D.continuation rootB)) := by
      rwa [hrootB_comp]
    have hvp := visitPosition_eq_of_pow T rootB
      (D.incoming c (otherBranch (firstVisitedBranch T c))) u hbase hu_lt hEq
    exact hne hvp.symm

theorem pow_portA_ne_incoming_of_lt_LA
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D))
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (s : ℕ)
    (hs1 : 1 ≤ s)
    (hs2 : s < Fintype.card (Fibre D.continuation
      (componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))))
    (j : Fin 2) :
    (D.continuation ^ s) (D.incoming c (firstVisitedBranch T c)) ≠ D.incoming c j := by
  have hs_comp : componentOf D.continuation
      ((D.continuation ^ s) (D.incoming c (firstVisitedBranch T c))) =
      componentOf D.continuation (D.incoming c (firstVisitedBranch T c)) :=
    componentOf_pow_apply D.continuation s (D.incoming c (firstVisitedBranch T c))
  intro hEq
  by_cases hj : j = firstVisitedBranch T c
  · subst hj
    have hdvd := (pow_apply_eq_self_iff_fibre_card_dvd D.continuation
      (D.incoming c (firstVisitedBranch T c)) s).mp hEq
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hs2) hdvd
  · have hj_other : j = otherBranch (firstVisitedBranch T c) :=
      eq_otherBranch_of_ne j (firstVisitedBranch T c) hj
    subst hj_other
    have hA_idx := affected_branch_A_componentIndex T r c hc
    have hB_idx := affected_branch_B_componentIndex_val T r c hc
    have hEq_idx : (T.componentIndex (componentOf D.continuation
        ((D.continuation ^ s) (D.incoming c (firstVisitedBranch T c))))).val =
        (T.componentIndex (componentOf D.continuation
          (D.incoming c (otherBranch (firstVisitedBranch T c))))).val :=
      congrArg (fun a => (T.componentIndex (componentOf D.continuation a)).val) hEq
    rw [hs_comp, hA_idx, hB_idx] at hEq_idx
    omega

theorem fused_pow_phase1
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (t : ℕ)
    (ht : t ≤ visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    ((smoothCrossing D c).continuation ^ t) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inl ((D.continuation ^ t) rootB)) := by
  intro rootB
  have hkB_lt := affected_kB_lt_LB T r hr c hc
  exact smooth_pow_eq_of_disjoint D c rootB
    (visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))))
    (fun u hu j => pow_rootB_ne_incoming_of_ne_kB T r hr c hc u
      (lt_trans hu hkB_lt) (ne_of_lt hu) j)
    t ht

theorem fused_pow_at_kB
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jB := otherBranch (firstVisitedBranch T c)
    let kB := visitPosition T (D.incoming c jB)
    ((smoothCrossing D c).continuation ^ kB) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inl (D.incoming c jB)) := by
  intro rootB jB kB
  rw [fused_pow_phase1 T r hr c hc kB (le_refl kB)]
  have hrec := visitPosition_reconstruct T (D.incoming c jB)
  rw [affected_branch_B_componentOf T r hr c hc] at hrec
  exact congrArg (fun a => smoothArcEquiv D (Sum.inl a)) hrec

theorem fused_pow_connector1
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jB := otherBranch (firstVisitedBranch T c)
    let kB := visitPosition T (D.incoming c jB)
    ((smoothCrossing D c).continuation ^ (kB + 1)) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inr jB) := by
  intro rootB jB kB
  rw [pow_succ', Perm.mul_apply, fused_pow_at_kB T r hr c hc,
    smooth_step_incoming D c jB]

theorem fused_pow_phase2
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let jB := otherBranch jA
    let kB := visitPosition T (D.incoming c jB)
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    ∀ s < LA,
      ((smoothCrossing D c).continuation ^ (kB + 2 + s)) (smoothArcEquiv D (Sum.inl rootB)) =
        smoothArcEquiv D (Sum.inl ((D.continuation ^ (s + 1)) (D.incoming c jA))) := by
  intro rootB jA jB kB LA s hs
  induction s with
  | zero =>
      have hexp : kB + 2 + 0 = (kB + 1) + 1 := by omega
      rw [hexp, pow_succ', Perm.mul_apply, fused_pow_connector1 T r hr c hc,
        smooth_step_connector D c jB, otherBranch_involutive, pow_one]
  | succ s ih =>
      have hs_lt : s + 1 < Fintype.card (Fibre D.continuation
          (componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))) := hs
      have hexp : kB + 2 + (s + 1) = (kB + 2 + s) + 1 := by omega
      rw [hexp, pow_succ', Perm.mul_apply, ih (Nat.lt_of_succ_lt hs),
        smooth_step_of_ne D c ((D.continuation ^ (s + 1)) (D.incoming c jA))
          (pow_portA_ne_incoming_of_lt_LA T r c hc (s + 1) (by omega) hs_lt)]
      congr 2
      simp [pow_succ', Perm.mul_apply]

theorem fused_pow_end_phase2
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let jB := otherBranch jA
    let kB := visitPosition T (D.incoming c jB)
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    ((smoothCrossing D c).continuation ^ (kB + LA + 1)) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inl (D.incoming c jA)) := by
  intro rootB jA jB kB LA
  have hLA_pos : 0 < LA := Fintype.card_pos_iff.mpr ⟨⟨D.incoming c jA, rfl⟩⟩
  have hLA_sub : LA - 1 < LA := Nat.sub_lt hLA_pos Nat.one_pos
  have hexp : kB + LA + 1 = kB + 2 + (LA - 1) := by omega
  have hexp2 : (LA - 1) + 1 = LA := Nat.sub_add_cancel hLA_pos
  rw [hexp, fused_pow_phase2 T r hr c hc (LA - 1) hLA_sub, hexp2,
    pow_card_fibre_apply D.continuation (D.incoming c jA)]

theorem fused_pow_connector2
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let jB := otherBranch jA
    let kB := visitPosition T (D.incoming c jB)
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    ((smoothCrossing D c).continuation ^ (kB + LA + 2)) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inr jA) := by
  intro rootB jA jB kB LA
  have hexp : kB + LA + 2 = (kB + LA + 1) + 1 := by omega
  rw [hexp, pow_succ', Perm.mul_apply, fused_pow_end_phase2 T r hr c hc,
    smooth_step_incoming D c jA]

theorem fused_pow_phase3_aux
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let jB := otherBranch jA
    let kB := visitPosition T (D.incoming c jB)
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    let LB := Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩))
    ∀ d ≤ LB - (kB + 1),
      ((smoothCrossing D c).continuation ^ (kB + 1 + d + LA + 2)) (smoothArcEquiv D (Sum.inl rootB)) =
        smoothArcEquiv D (Sum.inl ((D.continuation ^ (kB + 1 + d)) rootB)) := by
  intro rootB jA jB kB LA LB d hd
  have hkB_lt : kB < LB := affected_kB_lt_LB T r hr c hc
  induction d with
  | zero =>
      have hexp : kB + 1 + 0 + LA + 2 = (kB + LA + 2) + 1 := by omega
      have hrec := visitPosition_reconstruct T (D.incoming c jB)
      rw [affected_branch_B_componentOf T r hr c hc] at hrec
      rw [hexp, pow_succ', Perm.mul_apply, fused_pow_connector2 T r hr c hc,
        smooth_step_connector D c jA]
      have hexp2 : kB + 1 + 0 = kB + 1 := by omega
      rw [hexp2, pow_succ', Perm.mul_apply, hrec]
  | succ d ih =>
      have hu_lt : kB + 1 + d < Fintype.card (Fibre D.continuation
          (T.componentIndex.symm ⟨r.val + 1, hr⟩)) := by
        change kB + 1 + d < LB
        omega
      have hu_ne : kB + 1 + d ≠ visitPosition T
          (D.incoming c (otherBranch (firstVisitedBranch T c))) := by
        change kB + 1 + d ≠ kB
        omega
      have hexp : kB + 1 + (d + 1) + LA + 2 = (kB + 1 + d + LA + 2) + 1 := by omega
      have hexp2 : kB + 1 + (d + 1) = (kB + 1 + d) + 1 := by omega
      rw [hexp, pow_succ', Perm.mul_apply, ih (by omega),
        smooth_step_of_ne D c ((D.continuation ^ (kB + 1 + d)) rootB)
          (pow_rootB_ne_incoming_of_ne_kB T r hr c hc (kB + 1 + d) hu_lt hu_ne),
        hexp2, pow_succ', Perm.mul_apply]

theorem fused_pow_phase3
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (u : ℕ)
    (hu1 : visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) + 1 ≤ u)
    (hu2 : u ≤ Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩))) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    ((smoothCrossing D c).continuation ^ (u + LA + 2)) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inl ((D.continuation ^ u) rootB)) := by
  intro rootB jA LA
  let kB := visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c)))
  let LB := Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩))
  change kB + 1 ≤ u at hu1
  change u ≤ LB at hu2
  have hu_eq : u = kB + 1 + (u - (kB + 1)) := by omega
  have hd_le : u - (kB + 1) ≤ LB - (kB + 1) := by omega
  have h := fused_pow_phase3_aux T r hr c hc (u - (kB + 1)) hd_le
  change ((smoothCrossing D c).continuation ^ (kB + 1 + (u - (kB + 1)) + LA + 2))
      (smoothArcEquiv D (Sum.inl rootB)) =
    smoothArcEquiv D (Sum.inl ((D.continuation ^ (kB + 1 + (u - (kB + 1)))) rootB)) at h
  rw [← hu_eq] at h
  exact h

theorem fused_pow_close
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    let LB := Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩))
    ((smoothCrossing D c).continuation ^ (LB + LA + 2)) (smoothArcEquiv D (Sum.inl rootB)) =
      smoothArcEquiv D (Sum.inl rootB) := by
  intro rootB jA LA LB
  have hkB_lt : visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) < LB :=
    affected_kB_lt_LB T r hr c hc
  rw [fused_pow_phase3 T r hr c hc LB (by omega) (le_refl LB)]
  have hrootB_comp : componentOf D.continuation rootB =
      T.componentIndex.symm ⟨r.val + 1, hr⟩ :=
    (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).property
  have hLB_eq : LB = Fintype.card (Fibre D.continuation (componentOf D.continuation rootB)) := by
    dsimp [LB]
    rw [hrootB_comp]
  rw [hLB_eq, pow_card_fibre_apply D.continuation rootB]

theorem fused_pow_ne_rootB_of_pos_of_lt
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (t : ℕ) (ht_pos : 0 < t)
    (ht_lt : t < Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩)) +
      Fintype.card (Fibre D.continuation
        (componentOf D.continuation (D.incoming c (firstVisitedBranch T c)))) + 2) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    ((smoothCrossing D c).continuation ^ t) (smoothArcEquiv D (Sum.inl rootB)) ≠
      smoothArcEquiv D (Sum.inl rootB) := by
  intro rootB
  let B := T.componentIndex.symm ⟨r.val + 1, hr⟩
  let jA := firstVisitedBranch T c
  let jB := otherBranch jA
  let kB := visitPosition T (D.incoming c jB)
  let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
  let LB := Fintype.card (Fibre D.continuation B)
  change t < LB + LA + 2 at ht_lt
  have hrootB_comp : componentOf D.continuation rootB = B := (T.baseArc B).property
  have hLB_eq : Fintype.card (Fibre D.continuation (componentOf D.continuation rootB)) = LB := by
    dsimp [LB]
    rw [hrootB_comp]
  have hkB_lt : kB < LB := affected_kB_lt_LB T r hr c hc
  intro hEq
  by_cases h1 : t ≤ kB
  · rw [fused_pow_phase1 T r hr c hc t h1] at hEq
    have hpow := Sum.inl.inj ((smoothArcEquiv D).injective hEq)
    have hdvd := (pow_apply_eq_self_iff_fibre_card_dvd D.continuation rootB t).mp hpow
    rw [hLB_eq] at hdvd
    exact (Nat.not_dvd_of_pos_of_lt ht_pos (by omega)) hdvd
  · by_cases h2 : t = kB + 1
    · rw [h2, fused_pow_connector1 T r hr c hc] at hEq
      exact Sum.inr_ne_inl ((smoothArcEquiv D).injective hEq)
    · by_cases h3 : t < kB + 2 + LA
      · have hs_lt : t - (kB + 2) < LA := by omega
        have hs : t = kB + 2 + (t - (kB + 2)) := by omega
        rw [hs, fused_pow_phase2 T r hr c hc (t - (kB + 2)) hs_lt] at hEq
        have hpow := Sum.inl.inj ((smoothArcEquiv D).injective hEq)
        have hcomp_lhs : componentOf D.continuation
            ((D.continuation ^ (t - (kB + 2) + 1)) (D.incoming c jA)) =
            componentOf D.continuation (D.incoming c jA) :=
          componentOf_pow_apply D.continuation _ _
        have hIdx_lhs : (T.componentIndex (componentOf D.continuation
            ((D.continuation ^ (t - (kB + 2) + 1)) (D.incoming c jA)))).val = r.val := by
          rw [hcomp_lhs, affected_branch_A_componentIndex T r c hc]
        have hIdx_rhs : (T.componentIndex (componentOf D.continuation rootB)).val = r.val + 1 := by
          rw [hrootB_comp]
          dsimp [B]
          rw [T.componentIndex.apply_symm_apply]
        rw [hpow, hIdx_rhs] at hIdx_lhs
        omega
      · by_cases h4 : t = kB + LA + 2
        · rw [h4, fused_pow_connector2 T r hr c hc] at hEq
          exact Sum.inr_ne_inl ((smoothArcEquiv D).injective hEq)
        · have hu1 : kB + 1 ≤ t - (LA + 2) := by omega
          have hu2 : t - (LA + 2) ≤ LB := by omega
          have hu_lt : t - (LA + 2) < LB := by omega
          have hu_pos : 0 < t - (LA + 2) := by omega
          have hu_eq : t = (t - (LA + 2)) + LA + 2 := by omega
          rw [hu_eq, fused_pow_phase3 T r hr c hc (t - (LA + 2)) hu1 hu2] at hEq
          have hpow := Sum.inl.inj ((smoothArcEquiv D).injective hEq)
          have hdvd := (pow_apply_eq_self_iff_fibre_card_dvd D.continuation rootB (t - (LA + 2))).mp hpow
          rw [hLB_eq] at hdvd
          exact (Nat.not_dvd_of_pos_of_lt hu_pos hu_lt) hdvd

theorem fused_fibre_card_eq
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    let LB := Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩))
    Fintype.card (Fibre (smoothCrossing D c).continuation
      (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)))) =
      LB + LA + 2 := by
  intro rootB jA LA LB
  let M := Fintype.card (Fibre (smoothCrossing D c).continuation
    (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB))))
  have hM_pos : 0 < M := Fintype.card_pos_iff.mpr ⟨⟨smoothArcEquiv D (Sum.inl rootB), rfl⟩⟩
  have hclose := fused_pow_close T r hr c hc
  have hdvd : M ∣ (LB + LA + 2) :=
    (pow_apply_eq_self_iff_fibre_card_dvd (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl rootB)) (LB + LA + 2)).mp hclose
  have hle : M ≤ LB + LA + 2 := Nat.le_of_dvd (by omega) hdvd
  rcases lt_or_eq_of_le hle with hlt | hEq
  · have hpowM := pow_card_fibre_apply (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl rootB))
    exact False.elim (fused_pow_ne_rootB_of_pos_of_lt T r hr c hc M hM_pos hlt hpowM)
  · exact hEq

/-! ### Part 4: Fused Smoothing Traversal and Visit Order -/

def IsUnaffectedComp (D : PLLinkDiagram) (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (C : diagramComponent D) (C' : diagramComponent (smoothCrossing D c)) : Prop :=
  (T.componentIndex C).val ≠ r.val ∧
    (T.componentIndex C).val ≠ r.val + 1 ∧
    componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl (T.baseArc C).val)) = C'

theorem unaffected_pow_ne_incoming
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D))
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (C : diagramComponent D)
    (h1 : (T.componentIndex C).val ≠ r.val)
    (h2 : (T.componentIndex C).val ≠ r.val + 1)
    (t : ℕ) (j : Fin 2) :
    (D.continuation ^ t) (T.baseArc C).val ≠ D.incoming c j := by
  intro hEq
  have hcomp_t : componentOf D.continuation ((D.continuation ^ t) (T.baseArc C).val) = C := by
    rw [componentOf_pow_apply, (T.baseArc C).property]
  have hIdx : (T.componentIndex C).val =
      (T.componentIndex (componentOf D.continuation (D.incoming c j))).val := by
    rw [← hcomp_t, hEq]
  by_cases hj : j = firstVisitedBranch T c
  · subst hj
    rw [affected_branch_A_componentIndex T r c hc] at hIdx
    exact h1 hIdx
  · have hj_other : j = otherBranch (firstVisitedBranch T c) :=
      eq_otherBranch_of_ne j (firstVisitedBranch T c) hj
    subst hj_other
    rw [affected_branch_B_componentIndex_val T r c hc] at hIdx
    exact h2 hIdx

theorem isUnaffectedComp_unique
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D))
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    {C₁ C₂ : diagramComponent D} {C' : diagramComponent (smoothCrossing D c)}
    (h₁ : IsUnaffectedComp D T r c C₁ C')
    (h₂ : IsUnaffectedComp D T r c C₂ C') :
    C₁ = C₂ := by
  have hiff := smooth_sameCycle_unaffected_iff D c (T.baseArc C₁).val
    (unaffected_pow_ne_incoming T r c hc C₁ h₁.1 h₁.2.1)
    (smoothArcEquiv D (Sum.inl (T.baseArc C₂).val))
  obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp (h₂.2.2.trans h₁.2.2.symm)
  have hval : (T.baseArc C₂).val = b := Sum.inl.inj ((smoothArcEquiv D).injective hb_eq)
  calc
    C₁ = componentOf D.continuation (T.baseArc C₁).val := (T.baseArc C₁).property.symm
    _ = componentOf D.continuation b := hb_comp.symm
    _ = componentOf D.continuation (T.baseArc C₂).val := by rw [hval]
    _ = C₂ := (T.baseArc C₂).property

theorem isUnaffectedComp_ne_merged
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    {C : diagramComponent D} {C' : diagramComponent (smoothCrossing D c)}
    (h : IsUnaffectedComp D T r c C C') :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    C' ≠ componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)) := by
  intro rootB hEq
  have hiff := smooth_sameCycle_unaffected_iff D c (T.baseArc C).val
    (unaffected_pow_ne_incoming T r c hc C h.1 h.2.1)
    (smoothArcEquiv D (Sum.inl rootB))
  obtain ⟨b, hb_comp, hb_eq⟩ := hiff.mp (hEq.symm.trans h.2.2.symm)
  have hval : rootB = b := Sum.inl.inj ((smoothArcEquiv D).injective hb_eq)
  have hC : componentOf D.continuation rootB = C := by
    rw [hval, hb_comp, (T.baseArc C).property]
  have hB : componentOf D.continuation rootB = T.componentIndex.symm ⟨r.val + 1, hr⟩ :=
    (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).property
  have hCB : C = T.componentIndex.symm ⟨r.val + 1, hr⟩ := hC.symm.trans hB
  have hIdx : (T.componentIndex C).val = r.val + 1 := by
    rw [hCB, T.componentIndex.apply_symm_apply]
  exact h.2.1 hIdx

noncomputable def fusedSmoothWeight (D : PLLinkDiagram) (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (c : Fin D.nCrossing)
    (C' : diagramComponent (smoothCrossing D c)) : ℕ :=
  if h : ∃ C, IsUnaffectedComp D T r c C C' then
    (T.componentIndex (Classical.choose h)).val
  else
    r.val

noncomputable def fusedSmoothBaseArc (D : PLLinkDiagram) (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing)
    (C' : diagramComponent (smoothCrossing D c)) :
    {e : Fin (smoothCrossing D c).nArc //
      componentOf (smoothCrossing D c).continuation e = C'} :=
  let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
  if h : ∃ C, IsUnaffectedComp D T r c C C' then
    ⟨smoothArcEquiv D (Sum.inl (T.baseArc (Classical.choose h)).val),
      (Classical.choose_spec h).2.2⟩
  else if hM : C' = componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl rootB)) then
    ⟨smoothArcEquiv D (Sum.inl rootB), hM.symm⟩
  else
    Classical.choice (fibreNonempty (smoothCrossing D c).continuation C')

noncomputable def fusedSmoothTraversal (D : PLLinkDiagram) (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) :
    BasedTraversal (smoothCrossing D c) where
  componentIndex := equivFinOfWeight (fusedSmoothWeight D T r c)
  baseArc := fusedSmoothBaseArc D T r hr c

theorem fusedSmoothBaseArc_merged
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    ((fusedSmoothTraversal D T r hr c).baseArc
      (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)))).val =
      smoothArcEquiv D (Sum.inl rootB) := by
  intro rootB
  let C_merged := componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB))
  have hnot : ¬ ∃ C, IsUnaffectedComp D T r c C C_merged := by
    rintro ⟨C, hC⟩
    exact isUnaffectedComp_ne_merged T r hr c hc hC rfl
  change (fusedSmoothBaseArc D T r hr c C_merged).val = _
  unfold fusedSmoothBaseArc
  dsimp only
  rw [dif_neg hnot, dif_pos rfl]

theorem fusedSmoothWeight_merged
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    fusedSmoothWeight D T r c
      (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB))) =
      r.val := by
  intro rootB
  let C_merged := componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB))
  have hnot : ¬ ∃ C, IsUnaffectedComp D T r c C C_merged := by
    rintro ⟨C, hC⟩
    exact isUnaffectedComp_ne_merged T r hr c hc hC rfl
  unfold fusedSmoothWeight
  rw [dif_neg hnot]

theorem fused_componentOf_arc_in_B
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (a : Fin D.nArc)
    (ha : (T.componentIndex (componentOf D.continuation a)).val = r.val + 1) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)) := by
  intro rootB
  have ha_B : componentOf D.continuation a = T.componentIndex.symm ⟨r.val + 1, hr⟩ := by
    apply T.componentIndex.injective
    apply Fin.ext
    rw [ha, T.componentIndex.apply_symm_apply]
  have hrec := visitPosition_reconstruct T a
  rw [ha_B] at hrec
  have hu_lt : visitPosition T a <
      Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩)) := by
    have h := visitPosition_lt_card T a
    rwa [ha_B] at h
  by_cases hle : visitPosition T a ≤
      visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c)))
  · have hpow := fused_pow_phase1 T r hr c hc (visitPosition T a) hle
    dsimp only at hpow
    rw [hrec] at hpow
    rw [← hpow]
    exact componentOf_pow_apply (smoothCrossing D c).continuation _ _
  · have hpow := fused_pow_phase3 T r hr c hc (visitPosition T a) (by omega) (le_of_lt hu_lt)
    dsimp only at hpow
    rw [hrec] at hpow
    rw [← hpow]
    exact componentOf_pow_apply (smoothCrossing D c).continuation _ _

theorem fused_visitPosition_arc_in_B_le
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (a : Fin D.nArc)
    (ha : (T.componentIndex (componentOf D.continuation a)).val = r.val + 1)
    (hle : visitPosition T a ≤ visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c)))) :
    visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl a)) =
      visitPosition T a := by
  let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
  have ha_B : componentOf D.continuation a = T.componentIndex.symm ⟨r.val + 1, hr⟩ := by
    apply T.componentIndex.injective
    apply Fin.ext
    rw [ha, T.componentIndex.apply_symm_apply]
  have hrec := visitPosition_reconstruct T a
  rw [ha_B] at hrec
  have hpow := fused_pow_phase1 T r hr c hc (visitPosition T a) hle
  dsimp only at hpow
  rw [hrec] at hpow
  have hu_lt : visitPosition T a <
      Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩)) := by
    have h := visitPosition_lt_card T a
    rwa [ha_B] at h
  have hM := fused_fibre_card_eq T r hr c hc
  dsimp only at hM
  have hlt_M : visitPosition T a <
      Fintype.card (Fibre (smoothCrossing D c).continuation
        (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)))) := by
    rw [hM]
    omega
  exact visitPosition_eq_of_pow (fusedSmoothTraversal D T r hr c)
    (smoothArcEquiv D (Sum.inl rootB)) (smoothArcEquiv D (Sum.inl a))
    (visitPosition T a)
    (fusedSmoothBaseArc_merged T r hr c hc)
    hlt_M
    hpow

theorem fused_visitPosition_arc_in_B_gt
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (a : Fin D.nArc)
    (ha : (T.componentIndex (componentOf D.continuation a)).val = r.val + 1)
    (hgt : visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) < visitPosition T a) :
    let jA := firstVisitedBranch T c
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl a)) =
      visitPosition T a + LA + 2 := by
  intro jA LA
  let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
  have ha_B : componentOf D.continuation a = T.componentIndex.symm ⟨r.val + 1, hr⟩ := by
    apply T.componentIndex.injective
    apply Fin.ext
    rw [ha, T.componentIndex.apply_symm_apply]
  have hrec := visitPosition_reconstruct T a
  rw [ha_B] at hrec
  have hu_lt : visitPosition T a <
      Fintype.card (Fibre D.continuation (T.componentIndex.symm ⟨r.val + 1, hr⟩)) := by
    have h := visitPosition_lt_card T a
    rwa [ha_B] at h
  have hpow := fused_pow_phase3 T r hr c hc (visitPosition T a) (by omega) (le_of_lt hu_lt)
  dsimp only at hpow
  rw [hrec] at hpow
  have hM := fused_fibre_card_eq T r hr c hc
  dsimp only at hM
  have hlt_M : visitPosition T a + LA + 2 <
      Fintype.card (Fibre (smoothCrossing D c).continuation
        (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)))) := by
    rw [hM]
    dsimp [LA, jA]
    omega
  exact visitPosition_eq_of_pow (fusedSmoothTraversal D T r hr c)
    (smoothArcEquiv D (Sum.inl rootB)) (smoothArcEquiv D (Sum.inl a))
    (visitPosition T a + LA + 2)
    (fusedSmoothBaseArc_merged T r hr c hc)
    hlt_M
    hpow

theorem fused_arc_in_A_merged_and_bounds
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (a : Fin D.nArc)
    (ha : T.componentIndex (componentOf D.continuation a) = r) :
    let rootB := (T.baseArc (T.componentIndex.symm ⟨r.val + 1, hr⟩)).val
    let jA := firstVisitedBranch T c
    let jB := otherBranch jA
    let kB := visitPosition T (D.incoming c jB)
    let LA := Fintype.card (Fibre D.continuation (componentOf D.continuation (D.incoming c jA)))
    componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)) ∧
    kB < visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl a)) ∧
    visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl a)) < kB + LA + 2 := by
  intro rootB jA jB kB LA
  let q := D.continuation (D.incoming c jA)
  have hq_comp : componentOf D.continuation q = componentOf D.continuation (D.incoming c jA) :=
    componentOf_apply D.continuation (D.incoming c jA)
  have ha_comp : componentOf D.continuation a = componentOf D.continuation q := by
    rw [hq_comp]
    exact T.componentIndex.injective (ha.trans (affected_branch_A_componentIndex T r c hc).symm)
  let idx := (orbitEnumeration D.continuation q).symm ⟨a, ha_comp⟩
  let s := idx.val
  have hs_lt : s < LA := by
    have hlt := idx.isLt
    have hcard : Fintype.card (Fibre D.continuation (componentOf D.continuation q)) = LA :=
      Fintype.card_congr (Equiv.cast (congrArg (Fibre D.continuation) hq_comp))
    omega
  have hpow_q : (D.continuation ^ s) q = a := by
    have h := congrArg Subtype.val ((orbitEnumeration D.continuation q).apply_symm_apply ⟨a, ha_comp⟩)
    rwa [orbitEnumeration_apply_val] at h
  have hpow_jA : (D.continuation ^ (s + 1)) (D.incoming c jA) = a := by
    rw [pow_succ, Perm.mul_apply]
    exact hpow_q
  have hpow_sm := fused_pow_phase2 T r hr c hc s hs_lt
  change ((smoothCrossing D c).continuation ^ (kB + 2 + s)) (smoothArcEquiv D (Sum.inl rootB)) =
    smoothArcEquiv D (Sum.inl ((D.continuation ^ (s + 1)) (D.incoming c jA))) at hpow_sm
  rw [hpow_jA] at hpow_sm
  have hcomp_sm : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a)) =
      componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)) := by
    rw [← hpow_sm]
    exact componentOf_pow_apply (smoothCrossing D c).continuation _ _
  have hkB_lt := affected_kB_lt_LB T r hr c hc
  have hM := fused_fibre_card_eq T r hr c hc
  dsimp only at hM
  have hlt_M : kB + 2 + s <
      Fintype.card (Fibre (smoothCrossing D c).continuation
        (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootB)))) := by
    rw [hM]
    dsimp [kB, jB, LA, jA] at hs_lt ⊢
    omega
  have hvp : visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl a)) =
      kB + 2 + s :=
    visitPosition_eq_of_pow (fusedSmoothTraversal D T r hr c)
      (smoothArcEquiv D (Sum.inl rootB)) (smoothArcEquiv D (Sum.inl a))
      (kB + 2 + s)
      (fusedSmoothBaseArc_merged T r hr c hc)
      hlt_M
      hpow_sm
  refine ⟨hcomp_sm, by omega, by omega⟩

theorem fused_unaffected_arc_props
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (a : Fin D.nArc)
    (h1 : (T.componentIndex (componentOf D.continuation a)).val ≠ r.val)
    (h2 : (T.componentIndex (componentOf D.continuation a)).val ≠ r.val + 1) :
    let C := componentOf D.continuation a
    let C' := componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a))
    componentOf (smoothCrossing D c).continuation
      (smoothArcEquiv D (Sum.inl (T.baseArc C).val)) = C' ∧
    fusedSmoothWeight D T r c C' = (T.componentIndex C).val ∧
    visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl a)) =
      visitPosition T a := by
  intro C C'
  let rootC := (T.baseArc C).val
  have hrootC : componentOf D.continuation rootC = C := (T.baseArc C).property
  have hrec := visitPosition_reconstruct T a
  have hpow := smooth_pow_eq_of_disjoint D c rootC (visitPosition T a)
    (fun t _ j => unaffected_pow_ne_incoming T r c hc C h1 h2 t j)
    (visitPosition T a) (le_refl _)
  rw [hrec] at hpow
  have hC' : componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootC)) = C' := by
    dsimp [C']
    rw [← hpow]
    exact (componentOf_pow_apply (smoothCrossing D c).continuation _ _).symm
  have hex : ∃ C₀, IsUnaffectedComp D T r c C₀ C' := ⟨C, h1, h2, hC'⟩
  have huniq : Classical.choose hex = C :=
    isUnaffectedComp_unique T r c hc (Classical.choose_spec hex) ⟨h1, h2, hC'⟩
  have hw : fusedSmoothWeight D T r c C' = (T.componentIndex C).val := by
    unfold fusedSmoothWeight
    rw [dif_pos hex, huniq]
  have hbase : ((fusedSmoothTraversal D T r hr c).baseArc
      (componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl rootC)))).val =
      smoothArcEquiv D (Sum.inl rootC) := by
    rw [hC']
    change (fusedSmoothBaseArc D T r hr c C').val = _
    unfold fusedSmoothBaseArc
    dsimp only
    rw [dif_pos hex]
    dsimp
    rw [huniq]
  have hlt_a : visitPosition T a <
      Fintype.card (Fibre D.continuation (componentOf D.continuation rootC)) := by
    rw [hrootC]
    exact visitPosition_lt_card T a
  have hlt_sm := card_fibre_smooth_gt_of_pow_disjoint D c rootC (visitPosition T a) hlt_a
    (fun t _ j => unaffected_pow_ne_incoming T r c hc C h1 h2 t j)
  have hvp := visitPosition_eq_of_pow (fusedSmoothTraversal D T r hr c)
    (smoothArcEquiv D (Sum.inl rootC)) (smoothArcEquiv D (Sum.inl a))
    (visitPosition T a) hbase hlt_sm hpow
  exact ⟨hC', hw, hvp⟩

theorem fused_weight_arc
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (a : Fin D.nArc) :
    let C := componentOf D.continuation a
    let C' := componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a))
    fusedSmoothWeight D T r c C' =
      if (T.componentIndex C).val = r.val ∨ (T.componentIndex C).val = r.val + 1 then
        r.val
      else
        (T.componentIndex C).val := by
  intro C C'
  by_cases h1 : (T.componentIndex C).val = r.val
  · rw [if_pos (Or.inl h1)]
    have hcomp := (fused_arc_in_A_merged_and_bounds T r hr c hc a (Fin.ext h1)).1
    dsimp [C']
    rw [hcomp]
    exact fusedSmoothWeight_merged T r hr c hc
  · by_cases h2 : (T.componentIndex C).val = r.val + 1
    · rw [if_pos (Or.inr h2)]
      have hcomp := fused_componentOf_arc_in_B T r hr c hc a h2
      dsimp [C']
      rw [hcomp]
      exact fusedSmoothWeight_merged T r hr c hc
    · rw [if_neg (by tauto)]
      exact (fused_unaffected_arc_props T r hr c hc a h1 h2).2.1

theorem weight_lt_of_lt_of_not_pair (rv ca cb : ℕ)
    (hnot1 : ¬ (ca = rv ∧ cb = rv + 1))
    (hnot2 : ¬ (ca = rv + 1 ∧ cb = rv))
    (hlt : ca < cb) :
    (if ca = rv ∨ ca = rv + 1 then rv else ca) <
      (if cb = rv ∨ cb = rv + 1 then rv else cb) := by
  split_ifs <;> omega

theorem fused_rankBefore_unmixed
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (hA : HasNoSelfCrossings D (T.componentIndex.symm r))
    (c : Fin D.nCrossing) (hc : adjacentSwapAffectedCrossing T r c)
    (y : Fin D.nCrossing) (_hyc : y ≠ c)
    (hnot_aff : ¬ adjacentSwapAffectedCrossing T r y) :
    let W := fusedSmoothTraversal D T r hr c
    rankBefore
      (visitRank W (smoothArcEquiv D (Sum.inl (D.incoming y 0))))
      (visitRank W (smoothArcEquiv D (Sum.inl (D.incoming y 1)))) ↔
      rankBefore (visitRank T (D.incoming y 0)) (visitRank T (D.incoming y 1)) := by
  intro W
  let a := D.incoming y 0
  let b := D.incoming y 1
  let Ca := componentOf D.continuation a
  let Cb := componentOf D.continuation b
  let Ca' := componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl a))
  let Cb' := componentOf (smoothCrossing D c).continuation (smoothArcEquiv D (Sum.inl b))
  by_cases hcomp : Ca = Cb
  · have hnot_A : (T.componentIndex Ca).val ≠ r.val := by
      intro ha_r
      have ha_A : Ca = T.componentIndex.symm r := by
        rw [← Fin.ext ha_r, T.componentIndex.symm_apply_apply]
      have hb_A : Cb = T.componentIndex.symm r := hcomp.symm.trans ha_A
      exact hA y ha_A hb_A
    by_cases ha_B : (T.componentIndex Ca).val = r.val + 1
    · have hb_B : (T.componentIndex Cb).val = r.val + 1 := hcomp ▸ ha_B
      have hCa' := fused_componentOf_arc_in_B T r hr c hc a ha_B
      have hCb' := fused_componentOf_arc_in_B T r hr c hc b hb_B
      have hcomp' : Ca' = Cb' := hCa'.trans hCb'.symm
      unfold rankBefore visitRank
      dsimp only
      change (W.componentIndex Ca' < W.componentIndex Cb' ∨
        W.componentIndex Ca' = W.componentIndex Cb' ∧
          visitPosition W (smoothArcEquiv D (Sum.inl a)) <
            visitPosition W (smoothArcEquiv D (Sum.inl b))) ↔
        (T.componentIndex Ca < T.componentIndex Cb ∨
          T.componentIndex Ca = T.componentIndex Cb ∧
            visitPosition T a < visitPosition T b)
      rw [hcomp, hcomp']
      simp only [lt_irrefl, true_and, false_or]
      let kB := visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c)))
      by_cases hale : visitPosition T a ≤ kB <;> by_cases hble : visitPosition T b ≤ kB
      · rw [fused_visitPosition_arc_in_B_le T r hr c hc a ha_B hale,
            fused_visitPosition_arc_in_B_le T r hr c hc b hb_B hble]
      · rw [fused_visitPosition_arc_in_B_le T r hr c hc a ha_B hale,
            fused_visitPosition_arc_in_B_gt T r hr c hc b hb_B (not_le.mp hble)]
        omega
      · rw [fused_visitPosition_arc_in_B_gt T r hr c hc a ha_B (not_le.mp hale),
            fused_visitPosition_arc_in_B_le T r hr c hc b hb_B hble]
        omega
      · rw [fused_visitPosition_arc_in_B_gt T r hr c hc a ha_B (not_le.mp hale),
            fused_visitPosition_arc_in_B_gt T r hr c hc b hb_B (not_le.mp hble)]
        omega
    · have hb_not_A : (T.componentIndex Cb).val ≠ r.val := hcomp ▸ hnot_A
      have hb_not_B : (T.componentIndex Cb).val ≠ r.val + 1 := hcomp ▸ ha_B
      obtain ⟨hCa'_root, _, hvp_a⟩ := fused_unaffected_arc_props T r hr c hc a hnot_A ha_B
      obtain ⟨hCb'_root, _, hvp_b⟩ := fused_unaffected_arc_props T r hr c hc b hb_not_A hb_not_B
      have hcomp_ab : componentOf D.continuation a = componentOf D.continuation b := hcomp
      have hcomp' : Ca' = Cb' := hCa'_root.symm.trans (by rw [hcomp_ab]; exact hCb'_root)
      unfold rankBefore visitRank
      dsimp only
      change (W.componentIndex Ca' < W.componentIndex Cb' ∨
        W.componentIndex Ca' = W.componentIndex Cb' ∧
          visitPosition W (smoothArcEquiv D (Sum.inl a)) <
            visitPosition W (smoothArcEquiv D (Sum.inl b))) ↔
        (T.componentIndex Ca < T.componentIndex Cb ∨
          T.componentIndex Ca = T.componentIndex Cb ∧
            visitPosition T a < visitPosition T b)
      rw [hcomp, hcomp', hvp_a, hvp_b]
      simp
  · have hne_idx : (T.componentIndex Ca).val ≠ (T.componentIndex Cb).val :=
      fun h => hcomp (T.componentIndex.injective (Fin.ext h))
    have hnot1 : ¬ ((T.componentIndex Ca).val = r.val ∧ (T.componentIndex Cb).val = r.val + 1) := by
      rintro ⟨h0, h1⟩
      exact hnot_aff (Or.inl ⟨Fin.ext h0, h1⟩)
    have hnot2 : ¬ ((T.componentIndex Ca).val = r.val + 1 ∧ (T.componentIndex Cb).val = r.val) := by
      rintro ⟨h0, h1⟩
      exact hnot_aff (Or.inr ⟨h0, Fin.ext h1⟩)
    have hwa := fused_weight_arc T r hr c hc a
    have hwb := fused_weight_arc T r hr c hc b
    dsimp only at hwa hwb
    rcases lt_or_gt_of_ne hne_idx with hlt | hgt
    · have hw_lt : fusedSmoothWeight D T r c Ca' < fusedSmoothWeight D T r c Cb' := by
        rw [hwa, hwb]
        exact weight_lt_of_lt_of_not_pair r.val (T.componentIndex Ca).val (T.componentIndex Cb).val
          hnot1 hnot2 hlt
      have hW_lt : W.componentIndex Ca' < W.componentIndex Cb' :=
        equivFinOfWeight_lt_of_lt (fusedSmoothWeight D T r c) hw_lt
      have hT_lt : T.componentIndex Ca < T.componentIndex Cb := Fin.lt_iff_val_lt_val.mpr hlt
      exact ⟨fun _ => Or.inl hT_lt, fun _ => Or.inl hW_lt⟩
    · have hw_gt : fusedSmoothWeight D T r c Cb' < fusedSmoothWeight D T r c Ca' := by
        rw [hwa, hwb]
        exact weight_lt_of_lt_of_not_pair r.val (T.componentIndex Cb).val (T.componentIndex Ca).val
          (fun ⟨h0, h1⟩ => hnot2 ⟨h1, h0⟩) (fun ⟨h0, h1⟩ => hnot1 ⟨h1, h0⟩) hgt
      have hW_gt : W.componentIndex Cb' < W.componentIndex Ca' :=
        equivFinOfWeight_lt_of_lt (fusedSmoothWeight D T r c) hw_gt
      have hT_gt : T.componentIndex Cb < T.componentIndex Ca := Fin.lt_iff_val_lt_val.mpr hgt
      constructor
      · rintro (hW_lt | ⟨hW_eq, _⟩)
        · exact False.elim (lt_asymm hW_lt hW_gt)
        · exact False.elim ((ne_of_gt hW_gt) hW_eq)
      · rintro (hT_lt | ⟨hT_eq, _⟩)
        · exact False.elim (lt_asymm hT_lt hT_gt)
        · exact False.elim ((ne_of_gt hT_gt) hT_eq)

theorem firstVisitedBranch_of_same_component_lt
    {G : PLLinkDiagram} (U : BasedTraversal G) (x : Fin G.nCrossing) (j : Fin 2)
    (hcomp : componentOf G.continuation (G.incoming x j) =
      componentOf G.continuation (G.incoming x (otherBranch j)))
    (hlt : visitPosition U (G.incoming x j) <
      visitPosition U (G.incoming x (otherBranch j))) :
    firstVisitedBranch U x = j := by
  unfold firstVisitedBranch rankBefore visitRank
  fin_cases j
  · dsimp [otherBranch] at hcomp hlt ⊢
    rw [hcomp, if_pos (Or.inr ⟨rfl, hlt⟩)]
  · dsimp [otherBranch] at hcomp hlt ⊢
    rw [hcomp]
    have hnot : ¬ (U.componentIndex (componentOf G.continuation (G.incoming x 0)) <
        U.componentIndex (componentOf G.continuation (G.incoming x 0)) ∨
        U.componentIndex (componentOf G.continuation (G.incoming x 0)) =
          U.componentIndex (componentOf G.continuation (G.incoming x 0)) ∧
          visitPosition U (G.incoming x 0) < visitPosition U (G.incoming x 1)) := by
      rintro (h1 | ⟨_, h2⟩)
      · exact lt_irrefl _ h1
      · exact lt_asymm hlt h2
    rw [if_neg hnot]

/-! ### Part 5: Prefix-Switched Invariant and Fused Smoothing Descent -/

def IsPrefixSwitched (D : PLLinkDiagram) (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) : Prop :=
  let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
  (∀ y : Fin D.nCrossing, ¬ adjacentSwapAffectedCrossing T r y → ¬ badAt T y) ∧
  (∀ x y : Fin D.nCrossing,
    adjacentSwapAffectedCrossing T r x →
    adjacentSwapAffectedCrossing T r y →
    ¬ badAt T' x →
    badAt T' y →
    visitPosition T (D.incoming x (firstVisitedBranch T' x)) <
      visitPosition T (D.incoming y (firstVisitedBranch T' y)))

theorem affected_of_mem_badCrossings_of_isPrefixSwitched
    {D : PLLinkDiagram} {T : BasedTraversal D}
    {r : Fin (diagramComponentCount D)} {hr : r.val + 1 < diagramComponentCount D}
    (hPref : IsPrefixSwitched D T r hr)
    {y : Fin D.nCrossing}
    (hy : y ∈ badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr))) :
    adjacentSwapAffectedCrossing T r y := by
  by_contra hnot_aff
  have hy_bad' : badAt (reindexTraversalComponents T (adjacentComponentSwap r hr)) y := by
    simpa [badCrossings] using hy
  have hfb := firstVisitedBranch_reindex_adjacent_components_of_not_mixed T r hr y
    (by simpa [adjacentSwapAffectedCrossing] using hnot_aff)
  have hy_badT : badAt T y := by
    unfold badAt at hy_bad' ⊢
    rwa [← hfb]
  exact hPref.1 y hnot_aff hy_badT

theorem affected_visitPosition_B_ne_of_ne
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    {x y : Fin D.nCrossing} (hxy : x ≠ y)
    (hx : adjacentSwapAffectedCrossing T r x)
    (hy : adjacentSwapAffectedCrossing T r y) :
    let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
    visitPosition T (D.incoming x (firstVisitedBranch T' x)) ≠
      visitPosition T (D.incoming y (firstVisitedBranch T' y)) := by
  intro T' hEq
  have hfb_x := firstVisitedBranch_reindex_adjacent_of_affected T r hr x hx
  have hfb_y := firstVisitedBranch_reindex_adjacent_of_affected T r hr y hy
  have hIdx_x := affected_branch_B_componentIndex_val T r x hx
  have hIdx_y := affected_branch_B_componentIndex_val T r y hy
  rw [← hfb_x] at hIdx_x
  rw [← hfb_y] at hIdx_y
  have hRank : visitRank T (D.incoming x (firstVisitedBranch T' x)) =
      visitRank T (D.incoming y (firstVisitedBranch T' y)) :=
    Prod.ext (Fin.ext (hIdx_x.trans hIdx_y.symm)) hEq
  have hArc : D.incoming x (firstVisitedBranch T' x) =
      D.incoming y (firstVisitedBranch T' y) :=
    visitRank_injective T hRank
  exact incoming_ne_of_crossing_ne D y x hxy
    (firstVisitedBranch T' x) (firstVisitedBranch T' y) hArc

theorem badCrossings_fusedSmoothTraversal_eq_empty
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (hA : HasNoSelfCrossings D (T.componentIndex.symm r))
    (hPref : IsPrefixSwitched D T r hr)
    (c : Fin D.nCrossing)
    (hc_mem : c ∈ badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr)))
    (hc_min : ∀ y ∈ badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr)),
      visitPosition T (D.incoming c (firstVisitedBranch
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) c)) ≤
      visitPosition T (D.incoming y (firstVisitedBranch
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) y))) :
    badCrossings (fusedSmoothTraversal D T r hr c) = ∅ := by
  let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
  let W := fusedSmoothTraversal D T r hr c
  have hc_aff : adjacentSwapAffectedCrossing T r c :=
    affected_of_mem_badCrossings_of_isPrefixSwitched hPref hc_mem
  have hc_bad : badAt T' c := by simpa [badCrossings] using hc_mem
  apply (badCrossings_eq_empty_iff_firstVisited_over W).mpr
  intro y'
  obtain ⟨⟨y, hyc⟩, rfl⟩ := (smoothCrossingEquiv D c).surjective y'
  change firstVisitedBranch W (smoothCrossingEquiv D c ⟨y, hyc⟩) =
    D.overBranch (((smoothCrossingEquiv D c).symm (smoothCrossingEquiv D c ⟨y, hyc⟩)).val)
  rw [Equiv.symm_apply_apply]
  by_cases hy_aff : adjacentSwapAffectedCrossing T r y
  · let jA := firstVisitedBranch T y
    let jB := firstVisitedBranch T' y
    have hjB_eq : jB = otherBranch jA :=
      firstVisitedBranch_reindex_adjacent_of_affected T r hr y hy_aff
    have hjA_eq : jA = otherBranch jB := by
      rw [hjB_eq, otherBranch_involutive]
    have hy_A_idx : T.componentIndex (componentOf D.continuation (D.incoming y jA)) = r :=
      affected_branch_A_componentIndex T r y hy_aff
    have hy_B_idx : (T.componentIndex (componentOf D.continuation (D.incoming y jB))).val = r.val + 1 := by
      rw [hjB_eq]
      exact affected_branch_B_componentIndex_val T r y hy_aff
    obtain ⟨hcomp_yA, hvp_yA_gt, hvp_yA_lt⟩ :=
      fused_arc_in_A_merged_and_bounds T r hr c hc_aff (D.incoming y jA) hy_A_idx
    have hcomp_yB := fused_componentOf_arc_in_B T r hr c hc_aff (D.incoming y jB) hy_B_idx
    have hfb_c : firstVisitedBranch T' c = otherBranch (firstVisitedBranch T c) :=
      firstVisitedBranch_reindex_adjacent_of_affected T r hr c hc_aff
    have hne_vp : visitPosition T (D.incoming y jB) ≠
        visitPosition T (D.incoming c (firstVisitedBranch T' c)) :=
      affected_visitPosition_B_ne_of_ne T r hr hyc hy_aff hc_aff
    have hin_jA := smoothCrossing_incoming_retained D c y hyc jA
    have hin_jB := smoothCrossing_incoming_retained D c y hyc jB
    rcases lt_or_gt_of_ne hne_vp with hlt_c | hgt_c
    · have hy_not_bad : ¬ badAt T' y := by
        intro hy_bad
        have hmem_y : y ∈ badCrossings T' := by simp [badCrossings, hy_bad]
        have hle : visitPosition T (D.incoming c (firstVisitedBranch T' c)) ≤
            visitPosition T (D.incoming y jB) := hc_min y hmem_y
        omega
      have hover_y : D.overBranch y = jB := (Classical.not_not.mp hy_not_bad).symm
      have hle_c' : visitPosition T (D.incoming y jB) ≤
          visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) := by
        rw [← hfb_c]
        exact le_of_lt hlt_c
      have hvp_yB := fused_visitPosition_arc_in_B_le T r hr c hc_aff (D.incoming y jB)
        hy_B_idx hle_c'
      have hcomp_same : componentOf (smoothCrossing D c).continuation
          ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) jB) =
          componentOf (smoothCrossing D c).continuation
            ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) (otherBranch jB)) := by
        rw [hin_jB, ← hjA_eq, hin_jA, hcomp_yB, hcomp_yA]
      have hvp_lt : visitPosition W
          ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) jB) <
          visitPosition W
            ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) (otherBranch jB)) := by
        rw [hin_jB, ← hjA_eq, hin_jA]
        change visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl (D.incoming y jB))) <
          visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl (D.incoming y jA)))
        rw [hvp_yB]
        exact lt_of_le_of_lt hle_c' hvp_yA_gt
      rw [hover_y]
      exact firstVisitedBranch_of_same_component_lt W
        (smoothCrossingEquiv D c ⟨y, hyc⟩) jB hcomp_same hvp_lt
    · have hy_bad : badAt T' y := by
        by_contra hy_good
        have hlt : visitPosition T (D.incoming y jB) <
            visitPosition T (D.incoming c (firstVisitedBranch T' c)) :=
          hPref.2 y c hy_aff hc_aff hy_good hc_bad
        omega
      have hover_y : D.overBranch y = jA := by
        have hne_jB : D.overBranch y ≠ jB := Ne.symm hy_bad
        rw [hjA_eq]
        exact eq_otherBranch_of_ne (D.overBranch y) jB hne_jB
      have hgt_c' : visitPosition T (D.incoming c (otherBranch (firstVisitedBranch T c))) <
          visitPosition T (D.incoming y jB) := by
        rwa [← hfb_c]
      have hvp_yB := fused_visitPosition_arc_in_B_gt T r hr c hc_aff (D.incoming y jB)
        hy_B_idx hgt_c'
      dsimp only at hvp_yB
      have hcomp_same : componentOf (smoothCrossing D c).continuation
          ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) jA) =
          componentOf (smoothCrossing D c).continuation
            ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) (otherBranch jA)) := by
        rw [hin_jA, ← hjB_eq, hin_jB, hcomp_yA, hcomp_yB]
      have hvp_lt : visitPosition W
          ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) jA) <
          visitPosition W
            ((smoothCrossing D c).incoming (smoothCrossingEquiv D c ⟨y, hyc⟩) (otherBranch jA)) := by
        rw [hin_jA, ← hjB_eq, hin_jB]
        change visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl (D.incoming y jA))) <
          visitPosition (fusedSmoothTraversal D T r hr c) (smoothArcEquiv D (Sum.inl (D.incoming y jB)))
        rw [hvp_yB]
        exact lt_of_lt_of_le hvp_yA_lt (by omega)
      rw [hover_y]
      exact firstVisitedBranch_of_same_component_lt W
        (smoothCrossingEquiv D c ⟨y, hyc⟩) jA hcomp_same hvp_lt
  · have hy_goodT : firstVisitedBranch T y = D.overBranch y :=
      Classical.not_not.mp (hPref.1 y hy_aff)
    have hfb := firstVisitedBranch_smooth_eq_of_rankBefore D T c W y hyc
      (fused_rankBefore_unmixed T r hr hA c hc_aff y hyc hy_aff)
    exact hfb.trans hy_goodT

/-! ### Part 6: Universal Inductive Skein Telescope -/

theorem exists_min_of_nonempty {α : Type*} (S : Finset α) (hS : S.Nonempty) (f : α → ℕ) :
    ∃ c ∈ S, ∀ y ∈ S, f c ≤ f y := by
  classical
  have himg : (S.image f).Nonempty := hS.image f
  have hmem : (S.image f).min' himg ∈ S.image f := Finset.min'_mem _ himg
  obtain ⟨c, hcS, hfc⟩ := Finset.mem_image.mp hmem
  refine ⟨c, hcS, ?_⟩
  intro y hyS
  rw [hfc]
  exact Finset.min'_le _ (f y) (Finset.mem_image_of_mem f hyS)

theorem isPrefixSwitched_switch_min
    {D : PLLinkDiagram} (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (hPref : IsPrefixSwitched D T r hr)
    (c : Fin D.nCrossing)
    (hc_mem : c ∈ badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr)))
    (hc_min : ∀ y ∈ badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr)),
      visitPosition T (D.incoming c (firstVisitedBranch
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) c)) ≤
      visitPosition T (D.incoming y (firstVisitedBranch
        (reindexTraversalComponents T (adjacentComponentSwap r hr)) y))) :
    IsPrefixSwitched (switchCrossing D c) (switchTraversal T c) r hr := by
  let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
  have hc_aff : adjacentSwapAffectedCrossing T r c :=
    affected_of_mem_badCrossings_of_isPrefixSwitched hPref hc_mem
  refine ⟨?_, ?_⟩
  · intro y hy_not_aff
    have hyc : y ≠ c := fun h => hy_not_aff (h ▸ hc_aff)
    intro hy_bad_sw
    exact hPref.1 y hy_not_aff ((badAt_switch_same T c y hyc).mp hy_bad_sw)
  · intro x y hx_aff hy_aff hx_good_sw hy_bad_sw
    change ¬ badAt (switchTraversal T' c) x at hx_good_sw
    change badAt (switchTraversal T' c) y at hy_bad_sw
    have hyc : y ≠ c := by
      intro hEq
      have hc_bad : badAt T' c := by simpa [badCrossings] using hc_mem
      have hc_bad_sw : badAt (switchTraversal T' c) c := hEq ▸ hy_bad_sw
      exact ((badAt_switch_toggle T' c).mp hc_bad_sw) hc_bad
    have hy_bad : badAt T' y := (badAt_switch_same T' c y hyc).mp hy_bad_sw
    have hy_mem : y ∈ badCrossings T' := by simp [badCrossings, hy_bad]
    by_cases hxc : x = c
    · have hle := hc_min y hy_mem
      have hne := affected_visitPosition_B_ne_of_ne T r hr (hxc ▸ hyc.symm) hx_aff hy_aff
      have hle' : visitPosition T (D.incoming x (firstVisitedBranch T' x)) ≤
          visitPosition T (D.incoming y (firstVisitedBranch T' y)) := hxc.symm ▸ hle
      exact lt_of_le_of_ne hle' hne
    · have hx_good : ¬ badAt T' x :=
        fun hx_bad => hx_good_sw ((badAt_switch_same T' c x hxc).mpr hx_bad)
      exact hPref.2 x y hx_aff hy_aff hx_good hy_bad

theorem isPrefixSwitched_of_descending
    {D : PLLinkDiagram} (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D) :
    IsPrefixSwitched D T r hr := by
  refine ⟨?_, ?_⟩
  · intro y _ hy_bad
    have hmem : y ∈ badCrossings T := by simp [badCrossings, hy_bad]
    rw [hT] at hmem
    exact Finset.not_mem_empty y hmem
  · intro x _ hx_aff _ hx_good _
    have hx_bad := (badAt_adjacentSwap_of_descending T hT r hr x).mpr hx_aff
    exact False.elim (hx_good hx_bad)

theorem prefixSwitched_telescope_aux {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (hA : HasNoSelfCrossings D (T.componentIndex.symm r))
    (hPref : IsPrefixSwitched D T r hr) :
    let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
    let Q := unlinkFactor ^ (diagramComponentCount D - 2)
    unlinkFactor * descendingLaurentEvaluator D T' - Q =
      (∏ c ∈ badCrossings T', pivotSwitchFactor D c) *
        (unlinkFactor * descendingUnlinkValue D - Q) := by
  classical
  intro T' Q
  by_cases hne : (badCrossings T').Nonempty
  · obtain ⟨c, hc_mem, hc_min⟩ := exists_min_of_nonempty (badCrossings T') hne
      (fun y => visitPosition T (D.incoming y (firstVisitedBranch T' y)))
    have hc_aff : adjacentSwapAffectedCrossing T r c :=
      affected_of_mem_badCrossings_of_isPrefixSwitched hPref hc_mem
    have hjoin : ¬ D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1) :=
      affected_not_sameCycle T r c hc_aff
    have hge2 : 2 ≤ diagramComponentCount D := by omega
    have hskein := descendingEvaluator_eq_any_pivot outer D hD T' c
    rw [descendingEvaluatorPivotBranch] at hskein
    let W := fusedSmoothTraversal D T r hr c
    have hW_empty : badCrossings W = ∅ :=
      badCrossings_fusedSmoothTraversal_eq_empty T r hr hA hPref c hc_mem hc_min
    have hdrop_c := smoothCrossing_crossing_count_drop D c
    have hlt_c : (smoothCrossing D c).nCrossing < n := by omega
    have hsm_eq_W : descendingLaurentEvaluator (smoothCrossing D c) (smoothChildBasedTraversal D c) =
        descendingLaurentEvaluator (smoothCrossing D c) W :=
      outer.1 (SignedDiagramIso.refl (smoothCrossing D c)) hlt_c
        (smoothChildBasedTraversal D c) W
    have hW_eval : descendingLaurentEvaluator (smoothCrossing D c) W = Q := by
      rw [descendingLaurentEvaluator_terminal (smoothCrossing D c) W (by simp [hW_empty])]
      exact descendingUnlinkValue_smooth_join D c hjoin hge2
    rw [hsm_eq_W, hW_eval] at hskein
    have hstep := skein_step_telescope_identity D c
      (descendingLaurentEvaluator D T')
      (descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T' c))
      Q hskein
    have hPref_sw : IsPrefixSwitched (switchCrossing D c) (switchTraversal T c) r hr :=
      isPrefixSwitched_switch_min T r hr hPref c hc_mem hc_min
    have ih := prefixSwitched_telescope_aux outer (switchCrossing D c) hD
      (switchTraversal T c) r hr hA hPref_sw
    dsimp only at ih
    have hbad_sw : badCrossings (switchTraversal T' c) = (badCrossings T').erase c :=
      badCrossings_switch_erase T' c hc_mem
    have hprod_sw : (∏ y ∈ (badCrossings T').erase c, pivotSwitchFactor (switchCrossing D c) y) =
        ∏ y ∈ (badCrossings T').erase c, pivotSwitchFactor D y := by
      apply Finset.prod_congr rfl
      intro y hy
      have hyc : y ≠ c := Finset.ne_of_mem_erase hy
      unfold pivotSwitchFactor
      rw [crossingSign_switchCrossing_of_ne D c y hyc]
    have hprod_mul : pivotSwitchFactor D c * (∏ y ∈ (badCrossings T').erase c, pivotSwitchFactor D y) =
        ∏ y ∈ badCrossings T', pivotSwitchFactor D y :=
      Finset.mul_prod_erase (badCrossings T') (pivotSwitchFactor D) hc_mem
    have ih' : unlinkFactor * descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T' c) - Q =
        (∏ y ∈ (badCrossings T').erase c, pivotSwitchFactor D y) *
          (unlinkFactor * descendingUnlinkValue D - Q) := by
      rw [← hprod_sw, ← hbad_sw]
      exact ih
    calc
      unlinkFactor * descendingLaurentEvaluator D T' - Q =
          pivotSwitchFactor D c *
            (unlinkFactor * descendingLaurentEvaluator (switchCrossing D c) (switchTraversal T' c) - Q) := hstep
      _ = pivotSwitchFactor D c *
            ((∏ y ∈ (badCrossings T').erase c, pivotSwitchFactor D y) *
              (unlinkFactor * descendingUnlinkValue D - Q)) := by rw [ih']
      _ = (pivotSwitchFactor D c * (∏ y ∈ (badCrossings T').erase c, pivotSwitchFactor D y)) *
            (unlinkFactor * descendingUnlinkValue D - Q) := by ring
      _ = (∏ c ∈ badCrossings T', pivotSwitchFactor D c) *
            (unlinkFactor * descendingUnlinkValue D - Q) := by rw [hprod_mul]
  · have hEmpty : badCrossings T' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hEval : descendingLaurentEvaluator D T' = descendingUnlinkValue D :=
      descendingLaurentEvaluator_terminal D T' (by simp [hEmpty])
    rw [hEval, hEmpty, Finset.prod_empty, one_mul]
termination_by (badCrossings (reindexTraversalComponents T (adjacentComponentSwap r hr))).card
decreasing_by
  change (badCrossings (switchTraversal T' c)).card < (badCrossings T').card
  have hdrop := badCrossings_switch_card T' c hc_mem
  omega

theorem descending_adjacentSwap_of_upper_no_self_of_prod_eq_one {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (hA : HasNoSelfCrossings D (T.componentIndex.symm r))
    (hProd : (∏ c ∈ Finset.univ.filter (adjacentSwapAffectedCrossing T r),
      pivotSwitchFactor D c) = 1) :
    descendingLaurentEvaluator D
      (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
        descendingUnlinkValue D := by
  let T' := reindexTraversalComponents T (adjacentComponentSwap r hr)
  let Q := unlinkFactor ^ (diagramComponentCount D - 2)
  have hPref : IsPrefixSwitched D T r hr := isPrefixSwitched_of_descending T hT r hr
  have hTel := prefixSwitched_telescope_aux outer D hD T r hr hA hPref
  dsimp only at hTel
  have hBadEq : badCrossings T' = Finset.univ.filter (adjacentSwapAffectedCrossing T r) :=
    badCrossings_adjacentSwap_of_descending T hT r hr
  rw [hBadEq, hProd, one_mul] at hTel
  have hMul : unlinkFactor * descendingLaurentEvaluator D T' =
      unlinkFactor * descendingUnlinkValue D := by
    calc
      unlinkFactor * descendingLaurentEvaluator D T' =
          (unlinkFactor * descendingLaurentEvaluator D T' - Q) + Q := by ring
      _ = (unlinkFactor * descendingUnlinkValue D - Q) + Q := by rw [hTel]
      _ = unlinkFactor * descendingUnlinkValue D := by ring
  exact unlinkFactor_mul_injective hMul

theorem descending_adjacentSwap_of_prod_eq_one {n : ℕ}
    (outer : LowerCrossingEvaluatorSkeinIH n)
    (D : PLLinkDiagram) (hD : D.nCrossing = n)
    (T : BasedTraversal D) (hT : badCrossings T = ∅)
    (r : Fin (diagramComponentCount D)) (hr : r.val + 1 < diagramComponentCount D)
    (hProd : HasNoSelfCrossings D (T.componentIndex.symm r) →
      (∏ c ∈ Finset.univ.filter (adjacentSwapAffectedCrossing T r),
        pivotSwitchFactor D c) = 1) :
    descendingLaurentEvaluator D
      (reindexTraversalComponents T (adjacentComponentSwap r hr)) =
        descendingUnlinkValue D := by
  by_cases hA : HasNoSelfCrossings D (T.componentIndex.symm r)
  · exact descending_adjacentSwap_of_upper_no_self_of_prod_eq_one outer D hD T hT r hr hA (hProd hA)
  · unfold HasNoSelfCrossings diagramComponent at hA
    push_neg at hA
    obtain ⟨c, h0, h1⟩ := hA
    have hself : D.continuation.SameCycle (D.incoming c 0) (D.incoming c 1) :=
      (componentOf_eq_iff _ _ _).mp (h0.trans h1.symm)
    have hIdx : T.componentIndex (componentOf D.continuation (D.incoming c 0)) = r := by
      rw [h0]
      exact T.componentIndex.apply_symm_apply r
    exact descending_adjacentSwap_of_selfCrossing outer D hD T hT r hr c hself (Or.inl hIdx)

end

end DirectGLSSW.HOMFLY.Gemini
