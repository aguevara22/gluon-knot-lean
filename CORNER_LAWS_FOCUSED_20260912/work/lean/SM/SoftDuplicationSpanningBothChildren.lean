import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import SM.InsertionIndices
import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InteriorCutSet
import Mathlib.Data.Subtype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import SM.NearFar
import SM.CompositionCutSet
import SM.ConsecutiveTriples
import SM.FarOnlyOutput
import SM.ConsecutiveCuts
import SM.InteriorCutIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import SM.CompositionSegments
import SM.NearFarTriangular
import SM.SegmentStability
import SM.G1Consequences
import SM.GenericTopology
import SM.CyclicChambers
import SM.SoftDuplicationIndices
import SM.SoftDuplicationCutFibers
import SM.SoftDuplicationPresentations
import SM.OrderedBoundaryTransport
import SM.SoftDuplicationStartingChildren
import SM.SoftDuplicationArrays
import SM.SoftDuplicationSpanningCutPresentations
import SM.CutSetNearFar
import SM.CutSetNearFarNeighbors
import SM.SoftDuplicationSpanningCutNeighbors
import SM.SoftDuplicationStartingGatePositions
import SM.SoftDuplicationSpanningCutGatePositions
import SM.SoftDuplicationSectionTriples
import SM.SoftDuplicationStartingGateProducts
import SM.SoftDuplicationSpanningCutGateProducts
import SM.SoftDuplicationStartingChildFactors
import SM.SoftDuplicationSpanningOneCutChildFactors

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningBothChildren.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- An actual cut cannot lie strictly inside an actual consecutive child. -/
theorem spanning_core_child_side (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    K.right ≤ s ∨ s ≤ K.left := by
  by_cases hr : K.right ≤ s
  · exact Or.inl hr
  · right
    apply le_of_not_gt
    intro hl
    exact hK.2.2 s hs ⟨hl, lt_of_not_ge hr⟩

/-- In the both-cut presentation, left children retain A and right children
start at B. The branch is determined by the actual core right endpoint. -/
def spanningBothChild (s : Fin n) (K : BoundaryInterval n) : BoundaryInterval (n + 1) :=
  if K.right ≤ s then OrderedBoundaryTransport.interval (startingOldEmbedding s) K
  else OrderedBoundaryTransport.interval (startingTailEmbedding s) K

@[simp]
theorem spanningBothChild_of_right_le (s : Fin n) (K : BoundaryInterval n)
    (hr : K.right ≤ s) :
    spanningBothChild s K = OrderedBoundaryTransport.interval (startingOldEmbedding s) K :=
  if_pos hr

@[simp]
theorem spanningBothChild_of_left_ge (s : Fin n) (K : BoundaryInterval n)
    (hl : s ≤ K.left) :
    spanningBothChild s K = OrderedBoundaryTransport.interval (startingTailEmbedding s) K := by
  apply if_neg
  exact not_le_of_gt (lt_of_le_of_lt hl K.increasing)

/-- Each section preserves both collapsed endpoints, even before consecutiveness. -/
theorem spanningBothChild_collapse_endpoints (s : Fin n) (K : BoundaryInterval n) :
    collapse s (spanningBothChild s K).left = K.left ∧
      collapse s (spanningBothChild s K).right = K.right := by
  by_cases hr : K.right ≤ s
  · rw [spanningBothChild, if_pos hr]
    exact ⟨collapse_old s K.left, collapse_old s K.right⟩
  · rw [spanningBothChild, if_neg hr]
    exact ⟨collapse_startingTail s K.left, collapse_startingTail s K.right⟩

theorem spanningBothChild_ne_duplicate (s : Fin n) (K : BoundaryInterval n) :
    spanningBothChild s K ≠ duplicateInterval s := by
  intro he
  have hc := (collapse_endpoints_eq_iff s (spanningBothChild s K)).mpr he
  have hb := spanningBothChild_collapse_endpoints s K
  rw [hb.1, hb.2] at hc
  exact (ne_of_lt K.increasing) hc

/-- Collapse is the exact core interval, not just an equality of lengths. -/
theorem spanningBothChild_collapse (s : Fin n) (K : BoundaryInterval n)
    (hne : spanningBothChild s K ≠ duplicateInterval s) :
    collapseInterval s (spanningBothChild s K) hne = K := by
  have hb := spanningBothChild_collapse_endpoints s K
  exact BoundaryInterval.eq_of_endpoints hb.1 hb.2

theorem spanningBothChild_injective (s : Fin n) : Function.Injective (spanningBothChild s) := by
  intro K L he
  have hl := congrArg (fun J : BoundaryInterval (n + 1) => collapse s J.left) he
  have hr := congrArg (fun J : BoundaryInterval (n + 1) => collapse s J.right) he
  rw [(spanningBothChild_collapse_endpoints s K).1,
    (spanningBothChild_collapse_endpoints s L).1] at hl
  rw [(spanningBothChild_collapse_endpoints s K).2,
    (spanningBothChild_collapse_endpoints s L).2] at hr
  exact BoundaryInterval.eq_of_endpoints hl hr

/-- Left images end at or before A; right images begin at or after B. -/
theorem spanning_both_child_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    (spanningBothChild s K).right ≤ A s ∨ B s ≤ (spanningBothChild s K).left := by
  rcases spanning_core_child_side s I hI C hs K hK with hr | hl
  · left
    rw [spanningBothChild_of_right_le s K hr]
    change old s K.right ≤ A s
    rw [← old_self s]
    exact (old_strictMono s).monotone hr
  · right
    rw [spanningBothChild_of_left_ge s K hl]
    change B s ≤ startingTailEmbedding s K.left
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).monotone hl

/-- Every inherited both-row child is in the plain endpoint region. -/
theorem spanningBothChild_plain (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    ¬ intervalContainsBoth s (spanningBothChild s K) := by
  intro hb
  rcases spanning_both_child_bounds s I hI C hs K hK with hr | hl
  · exact (not_le_of_gt (A_lt_B s)) (le_trans hb.2 hr)
  · exact (not_le_of_gt (A_lt_B s)) (le_trans hl hb.1)

/-- On the left, adding B creates no interior cut because B is after the right endpoint. -/
theorem spanning_both_old_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hr : K.right ≤ s) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
  have hzero := (consecutive_ordered_image_iff (startingOldEmbedding s) C
    (spanningCutSet s I hI C hL hR hs 0)
    (spanningCutSet_zero_cuts s I hI C hL hR hs) K).mpr hK
  have hb : old s K.right < B s := by
    have ha : old s K.right ≤ A s := by
      rw [← old_self s]
      exact (old_strictMono s).monotone hr
    exact lt_of_le_of_lt ha (A_lt_B s)
  refine ⟨?_, ?_, ?_⟩
  · rw [spanningCutSet_two_insert_B]
    exact Finset.mem_insert_of_mem hzero.1
  · rw [spanningCutSet_two_insert_B]
    exact Finset.mem_insert_of_mem hzero.2.1
  · intro p hp hpbetween
    rw [spanningCutSet_two_insert_B] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact lt_asymm hb hpbetween.2
    · exact hzero.2.2 p hp hpbetween

/-- On the right, adding A creates no interior cut because A is before the left endpoint. -/
theorem spanning_both_tail_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hl : s ≤ K.left) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) := by
  have hone := (consecutive_ordered_image_iff (startingTailEmbedding s) C
    (spanningCutSet s I hI C hL hR hs 1)
    (spanningCutSet_one_cuts s I hI C hL hR hs) K).mpr hK
  have ha : A s < startingTailEmbedding s K.left := by
    have hb : B s ≤ startingTailEmbedding s K.left := by
      rw [← startingTail_self s]
      exact (startingTailEmbedding s).monotone hl
    exact lt_of_lt_of_le (A_lt_B s) hb
  refine ⟨?_, ?_, ?_⟩
  · rw [spanningCutSet_two_insert_A]
    exact Finset.mem_insert_of_mem hone.1
  · rw [spanningCutSet_two_insert_A]
    exact Finset.mem_insert_of_mem hone.2.1
  · intro p hp hpbetween
    rw [spanningCutSet_two_insert_A] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact lt_asymm ha hpbetween.1
    · exact hone.2.2 p hp hpbetween

theorem spanning_both_mapped_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive (spanningBothChild s K) := by
  rcases spanning_core_child_side s I hI C hs K hK with hr | hl
  · rw [spanningBothChild_of_right_le s K hr]
    exact spanning_both_old_consecutive s I hI C hL hR hs K hK hr
  · rw [spanningBothChild_of_left_ge s K hl]
    exact spanning_both_tail_consecutive s I hI C hL hR hs K hK hl

/-- The inserted singleton is an actual child since A and B are adjacent finite indices. -/
theorem spanning_both_duplicate_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive (duplicateInterval s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [spanningCutSet_two_insert_A]
    exact Finset.mem_insert_self _ _
  · rw [spanningCutSet_two_insert_B]
    exact Finset.mem_insert_self _ _
  · intro p _ hb
    have hl : s.val < p.val := hb.1
    have hr : p.val < s.val + 1 := hb.2
    omega

/-- Exhaustive endpoint classification on the actual both-row child subtype. -/
theorem spanning_both_child_trichotomy (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (spanningCutSet s I hI C hL hR hs 2).Consecutive J) :
    J = duplicateInterval s ∨ J.right ≤ A s ∨ B s ≤ J.left := by
  by_cases hr : J.right ≤ A s
  · exact Or.inr (Or.inl hr)
  · by_cases hl : B s ≤ J.left
    · exact Or.inr (Or.inr hl)
    · have hlA : J.left ≤ A s := by
        have hb : J.left.val < s.val + 1 := lt_of_not_ge hl
        change J.left.val ≤ s.val
        omega
      have hdup := spanning_both_duplicate_consecutive s I hI C hL hR hs
      have hleft : J.left = A s := by
        by_contra he
        exact hJ.2.2 (A s) hdup.1 ⟨lt_of_le_of_ne hlA he, lt_of_not_ge hr⟩
      exact Or.inl ((spanningCutSet s I hI C hL hR hs 2).consecutive_eq_of_left hJ hdup hleft)

/-- A left child stays consecutive after removing B; its endpoints cannot be B. -/
theorem spanning_both_left_zero_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (spanningCutSet s I hI C hL hR hs 2).Consecutive J)
    (hr : J.right ≤ A s) : (spanningCutSet s I hI C hL hR hs 0).Consecutive J := by
  have hright : J.right < B s := lt_of_le_of_lt hr (A_lt_B s)
  have hleft : J.left < B s := lt_trans J.increasing hright
  refine ⟨?_, ?_, ?_⟩
  · have hm := hJ.1
    rw [spanningCutSet_two_insert_B] at hm
    exact (Finset.mem_insert.mp hm).resolve_left (ne_of_lt hleft)
  · have hm := hJ.2.1
    rw [spanningCutSet_two_insert_B] at hm
    exact (Finset.mem_insert.mp hm).resolve_left (ne_of_lt hright)
  · intro p hp hb
    exact hJ.2.2 p (by rw [spanningCutSet_two_insert_B]; exact Finset.mem_insert_of_mem hp) hb

/-- A right child stays consecutive after removing A; its endpoints cannot be A. -/
theorem spanning_both_right_one_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (spanningCutSet s I hI C hL hR hs 2).Consecutive J)
    (hl : B s ≤ J.left) : (spanningCutSet s I hI C hL hR hs 1).Consecutive J := by
  have hleft : A s < J.left := lt_of_lt_of_le (A_lt_B s) hl
  have hright : A s < J.right := lt_trans hleft J.increasing
  refine ⟨?_, ?_, ?_⟩
  · have hm := hJ.1
    rw [spanningCutSet_two_insert_A] at hm
    exact (Finset.mem_insert.mp hm).resolve_left (ne_of_gt hleft)
  · have hm := hJ.2.1
    rw [spanningCutSet_two_insert_A] at hm
    exact (Finset.mem_insert.mp hm).resolve_left (ne_of_gt hright)
  · intro p hp hb
    exact hJ.2.2 p (by rw [spanningCutSet_two_insert_A]; exact Finset.mem_insert_of_mem hp) hb

/-- Both actual one-cut image exhaustions recover the complete core child domain. -/
theorem spanning_both_consecutive_iff (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) (J : BoundaryInterval (n + 1)) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive J ↔
      J = duplicateInterval s ∨ ∃ K : BoundaryInterval n,
        C.Consecutive K ∧ spanningBothChild s K = J := by
  constructor
  · intro hJ
    rcases spanning_both_child_trichotomy s I hI C hL hR hs J hJ with he | hr | hl
    · exact Or.inl he
    · right
      obtain ⟨K, hK, he⟩ := consecutive_ordered_image_exhaust (startingOldEmbedding s) C
        (spanningCutSet s I hI C hL hR hs 0) (spanningCutSet_zero_cuts s I hI C hL hR hs) J
        (spanning_both_left_zero_consecutive s I hI C hL hR hs J hJ hr)
      have hk : K.right ≤ s := by
        apply (old_strictMono s).le_iff_le.mp
        rw [old_self s]
        have heR := congrArg BoundaryInterval.right he
        change old s K.right = J.right at heR
        rw [heR]
        exact hr
      exact ⟨K, hK, (spanningBothChild_of_right_le s K hk).trans he⟩
    · right
      obtain ⟨K, hK, he⟩ := consecutive_ordered_image_exhaust (startingTailEmbedding s) C
        (spanningCutSet s I hI C hL hR hs 1) (spanningCutSet_one_cuts s I hI C hL hR hs) J
        (spanning_both_right_one_consecutive s I hI C hL hR hs J hJ hl)
      have hk : s ≤ K.left := by
        apply (startingTailEmbedding s).strictMono.le_iff_le.mp
        rw [startingTail_self s]
        have heL := congrArg BoundaryInterval.left he
        change startingTailEmbedding s K.left = J.left at heL
        rw [heL]
        exact hl
      exact ⟨K, hK, (spanningBothChild_of_left_ge s K hk).trans he⟩
  · rintro (rfl | ⟨K, hK, rfl⟩)
    · exact spanning_both_duplicate_consecutive s I hI C hL hR hs
    · exact spanning_both_mapped_consecutive s I hI C hL hR hs K hK

def spanningChildBothMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    Unit ⊕ {K : BoundaryInterval n // C.Consecutive K} →
      {J : BoundaryInterval (n + 1) // (spanningCutSet s I hI C hL hR hs 2).Consecutive J} :=
  Sum.elim (fun _ : Unit => ⟨duplicateInterval s, spanning_both_duplicate_consecutive s I hI C hL hR hs⟩)
    (fun K => ⟨spanningBothChild s K.val, spanning_both_mapped_consecutive s I hI C hL hR hs K.val K.property⟩)

/-- One duplicate child plus every actual core child is the entire both-row child domain. -/
def spanningChildrenBothEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (Unit ⊕ {K : BoundaryInterval n // C.Consecutive K}) ≃
      {J : BoundaryInterval (n + 1) // (spanningCutSet s I hI C hL hR hs 2).Consecutive J} :=
  Equiv.ofBijective (spanningChildBothMap s I hI C hL hR hs) ⟨by
    intro a b he
    cases a with
    | inl u =>
      cases b with
      | inl v => cases u; cases v; rfl
      | inr K =>
        have hx : duplicateInterval s = spanningBothChild s K.val := congrArg Subtype.val he
        exact False.elim (spanningBothChild_ne_duplicate s K.val hx.symm)
    | inr K =>
      cases b with
      | inl u =>
        have hx : spanningBothChild s K.val = duplicateInterval s := congrArg Subtype.val he
        exact False.elim (spanningBothChild_ne_duplicate s K.val hx)
      | inr L =>
        have hx : spanningBothChild s K.val = spanningBothChild s L.val := congrArg Subtype.val he
        exact congrArg Sum.inr (Subtype.ext (spanningBothChild_injective s hx)), by
    intro J
    rcases (spanning_both_consecutive_iff s I hI C hL hR hs J.val).mp J.property with he | ⟨K, hK, he⟩
    · exact ⟨Sum.inl (), Subtype.ext he.symm⟩
    · exact ⟨Sum.inr ⟨K, hK⟩, Subtype.ext he⟩⟩

@[simp]
theorem spanningChildrenBothEquiv_inl_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) (u : Unit) :
    ((spanningChildrenBothEquiv s I hI C hL hR hs) (Sum.inl u)).val = duplicateInterval s := rfl

@[simp]
theorem spanningChildrenBothEquiv_inr_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : {K : BoundaryInterval n // C.Consecutive K}) :
    ((spanningChildrenBothEquiv s I hI C hL hR hs) (Sum.inr K)).val = spanningBothChild s K.val := rfl

end
end SM.SoftDuplication
