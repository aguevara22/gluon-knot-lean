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

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationSpanningCutGatePositions.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Both strict spanning endpoints are fixed by the old section. -/
theorem spanning_old_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right) :
    old s (collapseInterval s I hI).left = I.left ∧
      old s (collapseInterval s I hI).right = I.right := by
  exact ⟨old_collapse_of_ne_B s I.left (ne_of_lt (lt_trans hL (A_lt_B s))),
    old_collapse_of_ne_B s I.right (ne_of_gt hR)⟩

/-- The tail section fixes the same actual outer endpoints, since neither is s. -/
theorem spanning_tail_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right) :
    startingTailEmbedding s (collapseInterval s I hI).left = I.left ∧
      startingTailEmbedding s (collapseInterval s I hI).right = I.right := by
  have hb := span_collapsed_bounds s I hL hR
  have he := spanning_old_endpoints s I hI hL hR
  exact ⟨(startingTail_eq_old s _ (ne_of_lt hb.1)).trans he.1,
    (startingTail_eq_old s _ (ne_of_gt hb.2)).trans he.2⟩

/-- Row zero retains exactly the old images of the core interior cuts. -/
theorem spanning_zero_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 0).interior.val = C.interior.val.image (old s) := by
  have he := spanning_old_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [spanningCutSet_zero_cuts] at hpc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hpc
    apply Finset.mem_image.mpr
    refine ⟨k, (starting_mem_interior_iff C k).mpr ⟨hk, ?_, ?_⟩, rfl⟩
    · apply (old_strictMono s).lt_iff_lt.mp
      exact lt_of_eq_of_lt he.1 hpl
    · apply (old_strictMono s).lt_iff_lt.mp
      exact lt_of_lt_of_eq hpr he.2.symm
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hkc, hkl, hkr⟩ := (starting_mem_interior_iff C k).mp hk
    apply (starting_mem_interior_iff _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [spanningCutSet_zero_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm (old_strictMono s hkl)
    · exact lt_of_lt_of_eq (old_strictMono s hkr) he.2

/-- Row one retains exactly the tail images of the core interior cuts. -/
theorem spanning_one_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 1).interior.val = C.interior.val.image (startingTailEmbedding s) := by
  have he := spanning_tail_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [spanningCutSet_one_cuts] at hpc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hpc
    apply Finset.mem_image.mpr
    refine ⟨k, (starting_mem_interior_iff C k).mpr ⟨hk, ?_, ?_⟩, rfl⟩
    · apply (startingTailEmbedding s).strictMono.lt_iff_lt.mp
      exact lt_of_eq_of_lt he.1 hpl
    · apply (startingTailEmbedding s).strictMono.lt_iff_lt.mp
      exact lt_of_lt_of_eq hpr he.2.symm
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hkc, hkl, hkr⟩ := (starting_mem_interior_iff C k).mp hk
    apply (starting_mem_interior_iff _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [spanningCutSet_one_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm ((startingTailEmbedding s).strictMono hkl)
    · exact lt_of_lt_of_eq ((startingTailEmbedding s).strictMono hkr) he.2

def spanningInteriorZeroMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (spanningCutSet s I hI C hL hR hs 0).interior.val} :=
  ⟨old s x.val, by
    rw [spanning_zero_interior]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- The actual old-position map, with every core interior cut represented once. -/
def spanningInteriorZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (spanningCutSet s I hI C hL hR hs 0).interior.val} :=
  Equiv.ofBijective (spanningInteriorZeroMap s I hI C hL hR hs) ⟨by
    intro x y he
    apply Subtype.ext
    exact old_injective s (congrArg Subtype.val he), by
    intro p
    have hp : p.val ∈ C.interior.val.image (old s) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (spanning_zero_interior s I hI C hL hR hs)) p.property
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp]
theorem spanningInteriorZeroEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((spanningInteriorZeroEquiv s I hI C hL hR hs) x).val = old s x.val := rfl

def spanningInteriorOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (spanningCutSet s I hI C hL hR hs 1).interior.val} :=
  ⟨startingTailEmbedding s x.val, by
    rw [spanning_one_interior]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- The actual tail-position map, with every core interior cut represented once. -/
def spanningInteriorOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (spanningCutSet s I hI C hL hR hs 1).interior.val} :=
  Equiv.ofBijective (spanningInteriorOneMap s I hI C hL hR hs) ⟨by
    intro x y he
    apply Subtype.ext
    exact (startingTailEmbedding s).injective (congrArg Subtype.val he), by
    intro p
    have hp : p.val ∈ C.interior.val.image (startingTailEmbedding s) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (spanning_one_interior s I hI C hL hR hs)) p.property
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp]
theorem spanningInteriorOneEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((spanningInteriorOneEquiv s I hI C hL hR hs) x).val = startingTailEmbedding s x.val := rfl

/-- The both row has exactly the inherited old interior cuts plus B. -/
theorem spanning_two_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).interior.val =
      insert (B s) (C.interior.val.image (old s)) := by
  rw [← spanning_zero_interior s I hI C hL hR hs]
  ext p
  simp only [starting_mem_interior_iff, spanningCutSet_two_insert_B, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hl, hr⟩
    exact hp.elim Or.inl (fun h => Or.inr ⟨h, hl, hr⟩)
  · rintro (rfl | ⟨hp, hl, hr⟩)
    · exact ⟨Or.inl rfl, lt_trans hL (A_lt_B s), hR⟩
    · exact ⟨Or.inr hp, hl, hr⟩

def spanningInteriorTwoMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    Unit ⊕ {k : Fin n // k ∈ C.interior.val} →
      {p : Fin (n + 1) // p ∈ (spanningCutSet s I hI C hL hR hs 2).interior.val}
  | Sum.inl _ => ⟨B s, by rw [spanning_two_interior]; exact Finset.mem_insert_self _ _⟩
  | Sum.inr x => ⟨old s x.val, by
      rw [spanning_two_interior]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)⟩

/-- The new B gate and all inherited gates form a disjoint, exhaustive domain. -/
def spanningInteriorTwoEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (Unit ⊕ {k : Fin n // k ∈ C.interior.val}) ≃
      {p : Fin (n + 1) // p ∈ (spanningCutSet s I hI C hL hR hs 2).interior.val} :=
  Equiv.ofBijective (spanningInteriorTwoMap s I hI C hL hR hs) ⟨by
    intro x y he
    have hv := congrArg Subtype.val he
    cases x with
    | inl u =>
      cases y with
      | inl v => cases u; cases v; rfl
      | inr y => exact False.elim (old_ne_B s y.val hv.symm)
    | inr x =>
      cases y with
      | inl u => exact False.elim (old_ne_B s x.val hv)
      | inr y => exact congrArg Sum.inr (Subtype.ext (old_injective s hv))
    , by
    intro p
    have hp : p.val ∈ insert (B s) (C.interior.val.image (old s)) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (spanning_two_interior s I hI C hL hR hs)) p.property
    rcases Finset.mem_insert.mp hp with he | hp
    · exact ⟨Sum.inl (), Subtype.ext he.symm⟩
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
      exact ⟨Sum.inr ⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp]
theorem spanningInteriorTwoEquiv_inl_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) (u : Unit) :
    ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inl u)).val = B s := rfl

@[simp]
theorem spanningInteriorTwoEquiv_inr_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)).val = old s x.val := rfl

/-- Both actual near neighbors in row zero are old images of core neighbors. -/
theorem spanning_zero_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (spanningCutSet s I hI C hL hR hs 0).nearAtCut
        ((spanningInteriorZeroEquiv s I hI C hL hR hs) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := spanningCutSet s I hI C hL hR hs 0
  let y := (spanningInteriorZeroEquiv s I hI C hL hR hs) x
  have hl := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (spanningCutSet_zero_cuts s I hI C hL hR hs) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (spanningCutSet_zero_cuts s I hI C hL hR hs) (C.nearRightInterval x)).mpr
      (C.nearRightInterval_consecutive x)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change old s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle])
  · change (S.nearAtCut y).middle = old s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change old s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle])

theorem spanning_zero_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (spanningCutSet s I hI C hL hR hs 0).farAtCut
        ((spanningInteriorZeroEquiv s I hI C hL hR hs) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := spanning_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((spanningCutSet s I hI C hL hR hs 0).farAtCut
        ((spanningInteriorZeroEquiv s I hI C hL hR hs) x)).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- Both actual near neighbors in row one are tail images of core neighbors. -/
theorem spanning_one_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (spanningCutSet s I hI C hL hR hs 1).nearAtCut
        ((spanningInteriorOneEquiv s I hI C hL hR hs) x) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.nearAtCut x) := by
  let S := spanningCutSet s I hI C hL hR hs 1
  let y := (spanningInteriorOneEquiv s I hI C hL hR hs) x
  have hl := (consecutive_ordered_image_iff (startingTailEmbedding s) C S
    (spanningCutSet_one_cuts s I hI C hL hR hs) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingTailEmbedding s) C S
    (spanningCutSet_one_cuts s I hI C hL hR hs) (C.nearRightInterval x)).mpr
      (C.nearRightInterval_consecutive x)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change startingTailEmbedding s (C.nearAtCut x).middle = startingTailEmbedding s x.val
      rw [C.nearAtCut_middle])
  · change (S.nearAtCut y).middle = startingTailEmbedding s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change startingTailEmbedding s (C.nearAtCut x).middle = startingTailEmbedding s x.val
      rw [C.nearAtCut_middle])

theorem spanning_one_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (spanningCutSet s I hI C hL hR hs 1).farAtCut
        ((spanningInteriorOneEquiv s I hI C hL hR hs) x) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.farAtCut x) := by
  have he := spanning_tail_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((spanningCutSet s I hI C hL hR hs 1).farAtCut
        ((spanningInteriorOneEquiv s I hI C hL hR hs) x)).middle =
      startingTailEmbedding s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- Inserting B cannot split an old-image child whose right cut is at most s. -/
theorem spanning_gate_two_old_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : K.right ≤ s) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
  have hzero := (consecutive_ordered_image_iff (startingOldEmbedding s) C
    (spanningCutSet s I hI C hL hR hs 0)
    (spanningCutSet_zero_cuts s I hI C hL hR hs) K).mpr hK
  have ha : old s K.right ≤ A s := by
    rw [← old_self s]
    exact (old_strictMono s).monotone hk
  have hb : old s K.right < B s := lt_of_le_of_lt ha (A_lt_B s)
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

/-- Inserting A cannot split a tail-image child whose left cut is at least s. -/
theorem spanning_gate_two_tail_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : s ≤ K.left) :
    (spanningCutSet s I hI C hL hR hs 2).Consecutive
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) := by
  have hone := (consecutive_ordered_image_iff (startingTailEmbedding s) C
    (spanningCutSet s I hI C hL hR hs 1)
    (spanningCutSet_one_cuts s I hI C hL hR hs) K).mpr hK
  have hb : B s ≤ startingTailEmbedding s K.left := by
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).monotone hk
  have ha : A s < startingTailEmbedding s K.left := lt_of_lt_of_le (A_lt_B s) hb
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

/-- Consecutiveness forbids the actual cut s strictly between a gate left of s
and its upper neighbor. -/
theorem spanning_gate_near_upper_le (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (x : {k : Fin n // k ∈ C.interior.val}) (hx : x.val < s) :
    (C.nearAtCut x).upper ≤ s := by
  apply le_of_not_gt
  intro h
  exact (C.nearRightInterval_consecutive x).2.2 s hs
    ⟨by change (C.nearAtCut x).middle < s; rw [C.nearAtCut_middle]; exact hx, h⟩

/-- The symmetric actual-neighbor bound follows from the left consecutive child. -/
theorem spanning_gate_near_lower_ge (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (x : {k : Fin n // k ∈ C.interior.val}) (hx : s < x.val) :
    s ≤ (C.nearAtCut x).lower := by
  apply le_of_not_gt
  intro h
  exact (C.nearLeftInterval_consecutive x).2.2 s hs
    ⟨h, by change s < (C.nearAtCut x).middle; rw [C.nearAtCut_middle]; exact hx⟩

/-- Left of the distinguished gate, both neighboring intervals are old images. -/
theorem spanning_two_nearTriple_of_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) (hx : x.val < s) :
    (spanningCutSet s I hI C hL hR hs 2).nearAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := spanningCutSet s I hI C hL hR hs 2
  let y := (spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)
  have hl := spanning_gate_two_old_consecutive s I hI C hL hR hs
    (C.nearLeftInterval x) (C.nearLeftInterval_consecutive x) (by
      change (C.nearAtCut x).middle ≤ s
      rw [C.nearAtCut_middle]
      exact hx.le)
  have hr := spanning_gate_two_old_consecutive s I hI C hL hR hs
    (C.nearRightInterval x) (C.nearRightInterval_consecutive x)
    (spanning_gate_near_upper_le s I hI C hs x hx)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change old s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle])
  · change (S.nearAtCut y).middle = old s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change old s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle])

/-- Right of the distinguished gate, both neighboring intervals are tail images. -/
theorem spanning_two_nearTriple_of_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) (hx : s < x.val) :
    (spanningCutSet s I hI C hL hR hs 2).nearAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.nearAtCut x) := by
  let S := spanningCutSet s I hI C hL hR hs 2
  let y := (spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)
  have he : startingTailEmbedding s x.val = old s x.val :=
    startingTail_eq_old s x.val (ne_of_gt hx)
  have hl := spanning_gate_two_tail_consecutive s I hI C hL hR hs
    (C.nearLeftInterval x) (C.nearLeftInterval_consecutive x)
    (spanning_gate_near_lower_ge s I hI C hs x hx)
  have hr := spanning_gate_two_tail_consecutive s I hI C hL hR hs
    (C.nearRightInterval x) (C.nearRightInterval_consecutive x) (by
      change s ≤ (C.nearAtCut x).middle
      rw [C.nearAtCut_middle]
      exact hx.le)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change startingTailEmbedding s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle, he])
  · change (S.nearAtCut y).middle = startingTailEmbedding s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle, he]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change startingTailEmbedding s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle, he])

/-- The inserted consecutive duplicate has no boundary index strictly inside it. -/
theorem spanning_gate_two_duplicate_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
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

/-- The old distinguished A has the genuine left child and [A,B] as neighbors. -/
theorem spanning_two_A_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    let T := (spanningCutSet s I hI C hL hR hs 2).nearAtCut
      ((spanningInteriorTwoEquiv s I hI C hL hR hs)
        (Sum.inr (spanningCoreCut s I hI C hL hR hs)))
    T.lower = old s (spanningLeftNeighbor s I hI C hL hR hs) ∧
      T.middle = A s ∧ T.upper = B s := by
  let S := spanningCutSet s I hI C hL hR hs 2
  let y := (spanningInteriorTwoEquiv s I hI C hL hR hs)
    (Sum.inr (spanningCoreCut s I hI C hL hR hs))
  have hl := spanning_gate_two_old_consecutive s I hI C hL hR hs
    (spanningLeftChild s I hI C hL hR hs) (spanning_left_child_consecutive s I hI C hL hR hs)
    (by rw [(spanning_left_child_endpoints s I hI C hL hR hs).2])
  have hy : y.val = A s := old_self s
  refine ⟨?_, ?_, ?_⟩
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change old s (spanningLeftChild s I hI C hL hR hs).right = y.val
      rw [(spanning_left_child_endpoints s I hI C hL hR hs).2, hy, old_self])
  · exact (S.nearAtCut_middle y).trans hy
  · exact S.nearAtCut_upper_eq_of_consecutive y (duplicateInterval s)
      (spanning_gate_two_duplicate_consecutive s I hI C hL hR hs) hy.symm

/-- The new B has [A,B] and the genuine right tail child as neighbors. -/
theorem spanning_two_B_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    let T := (spanningCutSet s I hI C hL hR hs 2).nearAtCut
      ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inl ()))
    T.lower = A s ∧ T.middle = B s ∧
      T.upper = startingTailEmbedding s (spanningRightNeighbor s I hI C hL hR hs) := by
  let S := spanningCutSet s I hI C hL hR hs 2
  let y := (spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inl ())
  have hr := spanning_gate_two_tail_consecutive s I hI C hL hR hs
    (spanningRightChild s I hI C hL hR hs) (spanning_right_child_consecutive s I hI C hL hR hs)
    (by rw [(spanning_right_child_endpoints s I hI C hL hR hs).1])
  refine ⟨?_, ?_, ?_⟩
  · exact S.nearAtCut_lower_eq_of_consecutive y (duplicateInterval s)
      (spanning_gate_two_duplicate_consecutive s I hI C hL hR hs) rfl
  · exact S.nearAtCut_middle y
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change startingTailEmbedding s (spanningRightChild s I hI C hL hR hs).left = B s
      rw [(spanning_right_child_endpoints s I hI C hL hR hs).1, startingTail_self])

/-- All inherited far triples use actual outer endpoints and their old mapped cut. -/
theorem spanning_two_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := spanning_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x))).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- In particular A's far triple is the old image of the actual core far at s. -/
theorem spanning_two_A_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs)
          (Sum.inr (spanningCoreCut s I hI C hL hR hs))) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s)
        (C.farAtCut (spanningCoreCut s I hI C hL hR hs)) :=
  spanning_two_farTriple s I hI C hL hR hs (spanningCoreCut s I hI C hL hR hs)

/-- B's far triple is the tail image of that same actual core far triple. -/
theorem spanning_two_B_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inl ())) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s)
        (C.farAtCut (spanningCoreCut s I hI C hL hR hs)) := by
  have he := spanning_tail_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inl ()))).middle =
      startingTailEmbedding s (C.farAtCut (spanningCoreCut s I hI C hL hR hs)).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    exact (startingTail_self s).symm
  · exact he.2.symm

/-- Off s, the actual far triple also equals the tail image; the outer endpoints
stay fixed and only the middle cut can distinguish the two sections. -/
theorem spanning_two_farTriple_of_ne (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (x : {k : Fin n // k ∈ C.interior.val}) (hx : x.val ≠ s) :
    (spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.farAtCut x) := by
  have he := spanning_tail_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((spanningCutSet s I hI C hL hR hs 2).farAtCut
        ((spanningInteriorTwoEquiv s I hI C hL hR hs) (Sum.inr x))).middle =
      startingTailEmbedding s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    exact (startingTail_eq_old s x.val hx).symm
  · exact he.2.symm

end
end SM.SoftDuplication
