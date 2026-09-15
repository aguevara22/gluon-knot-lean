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
import SM.SoftDuplicationSpanningBothChildren
import SM.SoftDuplicationSpanningBothChildFactors
import SM.SoftDuplicationSpanningCoreCancellation
import SM.SoftDuplicationSpanningEmptyChildren
import SM.SoftDuplicationSpanningEmptyGates
import SM.SoftDuplicationAvoiding
import SM.SoftDuplicationAvoidingCompositions
import SM.SoftDuplicationAvoidingUnit
import SM.SoftDuplicationAvoidingTransform
import SM.SoftDuplicationSpanningEmptyWeights
import SM.SoftDuplicationTransformSetup
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices
import SM.SoftInsertionSuccessors
import SM.SoftInsertionTuple
import SM.SoftLocalDeterminants
import SM.SoftFamilyG1
import SM.SoftAttachmentSigns
import SM.SoftFarSignFamily
import SM.SoftParentEdges
import SM.SoftRootBoundary
import SM.SoftDuplicationScalars
import SM.SoftGeometricDuplication
import SM.SoftDuplicationNeighbors
import SM.SoftDuplicationSpanningTransform
import SM.SoftDuplicationStartingTransform
import SM.SoftDuplicationEndingChildren

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/SoftDuplicationEndingGatePositions.body.lean (prototype SoftAmplitudeSource, kernel session 40796, receipt
SoftAmplitudeSource-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The tail section maps both collapsed ending-interval endpoints to the
actual parent endpoints, including its right endpoint B. -/
theorem ending_tail_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : I.right = B s) :
    startingTailEmbedding s (collapseInterval s I hI).left = I.left ∧
      startingTailEmbedding s (collapseInterval s I hI).right = I.right := by
  have hp : I.left ≠ B s := ne_of_lt (lt_trans hL (A_lt_B s))
  have hcs : collapse s I.left ≠ s := by
    intro he
    rcases (collapse_eq_s_iff s I.left).mp he with he | he
    · exact (ne_of_lt hL) he
    · exact hp he
  constructor
  · change startingTailEmbedding s (collapse s I.left) = I.left
    rw [startingTail_eq_old s _ hcs, old_collapse_of_ne_B s I.left hp]
  · rw [ending_core_right s I hI hR, startingTail_self, hR]

/-- Every inherited gate is strictly before the distinguished core endpoint. -/
theorem ending_interior_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hR : I.right = B s) (x : {k : Fin n // k ∈ C.interior.val}) : x.val < s := by
  have hx := (C.interior.property x.val x.property).2
  simpa only [ending_core_right s I hI hR] using hx

/-- The B-only row has exactly the tail images of the core interior cuts. -/
theorem ending_zero_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (endingCutSet s I hI C hL hR 0).interior.val =
      C.interior.val.image (startingTailEmbedding s) := by
  have he := ending_tail_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [endingCutSet_zero_cuts] at hpc
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
    · rw [endingCutSet_zero_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm ((startingTailEmbedding s).strictMono hkl)
    · exact lt_of_lt_of_eq ((startingTailEmbedding s).strictMono hkr) he.2

/-- The both-cut row adds precisely the retained occurrence A as an interior gate. -/
theorem ending_one_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (endingCutSet s I hI C hL hR 1).interior.val =
      insert (A s) (C.interior.val.image (startingTailEmbedding s)) := by
  rw [← ending_zero_interior s I hI C hL hR]
  ext p
  simp only [starting_mem_interior_iff, endingCutSet_one_insert_A, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hl, hr⟩
    exact hp.elim Or.inl (fun h => Or.inr ⟨h, hl, hr⟩)
  · rintro (rfl | ⟨hp, hl, hr⟩)
    · exact ⟨Or.inl rfl, hL, by rw [hR]; exact A_lt_B s⟩
    · exact ⟨Or.inr hp, hl, hr⟩

def endingInteriorZeroMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (endingCutSet s I hI C hL hR 0).interior.val} :=
  ⟨startingTailEmbedding s x.val, by
    rw [ending_zero_interior]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

def endingInteriorZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (endingCutSet s I hI C hL hR 0).interior.val} :=
  Equiv.ofBijective (endingInteriorZeroMap s I hI C hL hR) ⟨by
    intro x y he
    apply Subtype.ext
    exact (startingTailEmbedding s).injective (congrArg Subtype.val he), by
    intro p
    have hp : p.val ∈ C.interior.val.image (startingTailEmbedding s) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (ending_zero_interior s I hI C hL hR)) p.property
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp] theorem endingInteriorZeroEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((endingInteriorZeroEquiv s I hI C hL hR) x).val = startingTailEmbedding s x.val := rfl

def endingInteriorOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    Unit ⊕ {k : Fin n // k ∈ C.interior.val} →
      {p : Fin (n + 1) // p ∈ (endingCutSet s I hI C hL hR 1).interior.val}
  | Sum.inl _ => ⟨A s, by rw [ending_one_interior]; exact Finset.mem_insert_self _ _⟩
  | Sum.inr x => ⟨startingTailEmbedding s x.val, by
      rw [ending_one_interior]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)⟩

def endingInteriorOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    (Unit ⊕ {k : Fin n // k ∈ C.interior.val}) ≃
      {p : Fin (n + 1) // p ∈ (endingCutSet s I hI C hL hR 1).interior.val} :=
  Equiv.ofBijective (endingInteriorOneMap s I hI C hL hR) ⟨by
    intro x y he
    have hv := congrArg Subtype.val he
    cases x with
    | inl u =>
      cases y with
      | inl v => cases u; cases v; rfl
      | inr y => exact False.elim ((Fin.succAbove_ne (A s) y.val) hv.symm)
    | inr x =>
      cases y with
      | inl u => exact False.elim ((Fin.succAbove_ne (A s) x.val) hv)
      | inr y => exact congrArg Sum.inr (Subtype.ext ((startingTailEmbedding s).injective hv))
    , by
    intro p
    have hp : p.val ∈ insert (A s) (C.interior.val.image (startingTailEmbedding s)) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (ending_one_interior s I hI C hL hR)) p.property
    rcases Finset.mem_insert.mp hp with he | hp
    · exact ⟨Sum.inl (), Subtype.ext he.symm⟩
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
      exact ⟨Sum.inr ⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp] theorem endingInteriorOneEquiv_inl_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (u : Unit) :
    ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inl u)).val = A s := rfl

@[simp] theorem endingInteriorOneEquiv_inr_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)).val = startingTailEmbedding s x.val := rfl

/-- Both inherited near neighbors in row zero are mapped by the tail section. -/
theorem ending_zero_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (endingCutSet s I hI C hL hR 0).nearAtCut
        ((endingInteriorZeroEquiv s I hI C hL hR) x) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.nearAtCut x) := by
  let S := endingCutSet s I hI C hL hR 0
  let y := (endingInteriorZeroEquiv s I hI C hL hR) x
  have hl := (consecutive_ordered_image_iff (startingTailEmbedding s) C S
    (endingCutSet_zero_cuts s I hI C hL hR) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingTailEmbedding s) C S
    (endingCutSet_zero_cuts s I hI C hL hR) (C.nearRightInterval x)).mpr
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

theorem ending_zero_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (endingCutSet s I hI C hL hR 0).farAtCut
        ((endingInteriorZeroEquiv s I hI C hL hR) x) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.farAtCut x) := by
  have he := ending_tail_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((endingCutSet s I hI C hL hR 0).farAtCut
        ((endingInteriorZeroEquiv s I hI C hL hR) x)).middle =
      startingTailEmbedding s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- In row one the inherited near samples end at the retained occurrence A. -/
theorem ending_one_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (endingCutSet s I hI C hL hR 1).nearAtCut
        ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := endingCutSet s I hI C hL hR 1
  let y := (endingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)
  have hx : startingTailEmbedding s x.val = old s x.val :=
    startingTail_eq_old s x.val (ne_of_lt (ending_interior_lt s I hI C hR x))
  have hl := ending_one_mapped_consecutive s I hI C hL hR
    (C.nearLeftInterval x) (C.nearLeftInterval_consecutive x)
  have hr := ending_one_mapped_consecutive s I hI C hL hR
    (C.nearRightInterval x) (C.nearRightInterval_consecutive x)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change old s (C.nearAtCut x).middle = startingTailEmbedding s x.val
      rw [C.nearAtCut_middle, hx])
  · change (S.nearAtCut y).middle = old s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle]
    exact hx
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change old s (C.nearAtCut x).middle = startingTailEmbedding s x.val
      rw [C.nearAtCut_middle, hx])

/-- Far triples keep the full right endpoint B, even after A is inserted as a cut. -/
theorem ending_one_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (endingCutSet s I hI C hL hR 1).farAtCut
        ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.farAtCut x) := by
  have he := ending_tail_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((endingCutSet s I hI C hL hR 1).farAtCut
        ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inr x))).middle =
      startingTailEmbedding s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- The new A gate has the old last child on its left and [A,B] on its right. -/
theorem ending_new_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    let T := (endingCutSet s I hI C hL hR 1).nearAtCut
      ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inl ()))
    T.lower = old s (endingLastChild s I hI C).left ∧ T.middle = A s ∧ T.upper = B s := by
  let S := endingCutSet s I hI C hL hR 1
  let y := (endingInteriorOneEquiv s I hI C hL hR) (Sum.inl ())
  have hl := ending_one_mapped_consecutive s I hI C hL hR
    (endingLastChild s I hI C) (endingLastChild_consecutive s I hI C)
  have hr := ending_one_duplicate_consecutive s I hI C hL hR
  have he := ending_last_one_endpoints s I hI C hR
  refine ⟨?_, ?_, ?_⟩
  · exact (S.nearAtCut_lower_eq_of_consecutive y
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (endingLastChild s I hI C))
      hl he.2).trans he.1
  · exact S.nearAtCut_middle y
  · exact S.nearAtCut_upper_eq_of_consecutive y (duplicateInterval s) hr rfl

theorem ending_new_far_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) :
    let T := (endingCutSet s I hI C hL hR 1).farAtCut
      ((endingInteriorOneEquiv s I hI C hL hR) (Sum.inl ()))
    T.lower = I.left ∧ T.middle = A s ∧ T.upper = B s := by
  refine ⟨rfl, ?_, hR⟩
  exact (endingCutSet s I hI C hL hR 1).farAtCut_middle _

end
end SM.SoftDuplication
