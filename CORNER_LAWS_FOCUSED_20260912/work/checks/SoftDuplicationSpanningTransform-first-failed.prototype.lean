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

namespace SM.SoftDuplication

variable {n : ℕ}

/-- Retained occurrence of the distinguished core position. -/
def A (s : Fin n) : Fin (n + 1) := s.castSucc

/-- New occurrence immediately after A in the linear boundary word. -/
def B (s : Fin n) : Fin (n + 1) := s.succ

/-- Increasing old-position embedding that skips precisely B. -/
def old (s : Fin n) : Fin n → Fin (n + 1) := (B s).succAbove

/-- Collapse both occurrences to s, leaving earlier positions fixed and
subtracting one from every later child position. -/
def collapse (s : Fin n) : Fin (n + 1) → Fin n := s.predAbove

@[simp] theorem A_val (s : Fin n) : (A s).val = s.val := rfl

@[simp] theorem B_val (s : Fin n) : (B s).val = s.val + 1 := rfl

theorem A_lt_B (s : Fin n) : A s < B s := by
  change s.val < s.val + 1
  omega

/-- The old embedding includes the retained occurrence A and shifts exactly
the core positions strictly after it. -/
theorem old_val (s k : Fin n) :
    (old s k).val = if k.val ≤ s.val then k.val else k.val + 1 := by
  by_cases h : k ≤ s
  · have hval : k.val ≤ s.val := h
    rw [if_pos hval]
    change (s.succ.succAbove k).val = k.val
    rw [Fin.succAbove_succ_of_le s k h]
    rfl
  · have hval : ¬ k.val ≤ s.val := h
    rw [if_neg hval]
    change (s.succ.succAbove k).val = k.val + 1
    rw [Fin.succAbove_succ_of_lt s k (lt_of_not_ge h)]
    rfl

@[simp] theorem old_self (s : Fin n) : old s s = A s := Fin.succAbove_succ_self s

theorem old_strictMono (s : Fin n) : StrictMono (old s) := Fin.strictMono_succAbove (B s)

theorem old_injective (s : Fin n) : Function.Injective (old s) := (old_strictMono s).injective

theorem old_ne_B (s k : Fin n) : old s k ≠ B s := Fin.succAbove_ne (B s) k

/-- Exact numeric collapse formula, with equality to s on both A and B. -/
theorem collapse_val (s : Fin n) (p : Fin (n + 1)) :
    (collapse s p).val = if p.val ≤ s.val then p.val else p.val - 1 := by
  by_cases h : p.val ≤ s.val
  · rw [if_pos h]
    change (s.predAbove p).val = p.val
    rw [Fin.predAbove_of_le_castSucc s p (show p ≤ s.castSucc from h)]
    rfl
  · rw [if_neg h]
    change (s.predAbove p).val = p.val - 1
    rw [Fin.predAbove_of_castSucc_lt s p
      (show s.castSucc < p from Nat.lt_of_not_ge h)]
    rfl

@[simp] theorem collapse_A (s : Fin n) : collapse s (A s) = s := Fin.predAbove_castSucc_self s

@[simp] theorem collapse_B (s : Fin n) : collapse s (B s) = s := Fin.predAbove_succ_self s

@[simp] theorem collapse_old (s k : Fin n) : collapse s (old s k) = k := by
  change s.predAbove (s.succ.succAbove k) = k
  by_cases h : k ≤ s
  · rw [Fin.succAbove_succ_of_le s k h, Fin.predAbove_castSucc_of_le s k h]
  · rw [Fin.succAbove_succ_of_lt s k (lt_of_not_ge h),
      Fin.predAbove_succ_of_le s k (le_of_lt (lt_of_not_ge h))]

theorem collapse_leftInverse (s : Fin n) : Function.LeftInverse (collapse s) (old s) :=
  collapse_old s

theorem collapse_monotone (s : Fin n) : Monotone (collapse s) := Fin.predAbove_right_monotone s

/-- Every child position except B is recovered by its unique retained old
preimage; the exceptional position is not silently discarded. -/
theorem old_collapse_of_ne_B (s : Fin n) (p : Fin (n + 1)) (hp : p ≠ B s) :
    old s (collapse s p) = p := Fin.succ_succAbove_predAbove hp

theorem child_exhaust (s : Fin n) (p : Fin (n + 1)) :
    p = B s ∨ ∃ k : Fin n, old s k = p := by
  by_cases hp : p = B s
  · exact Or.inl hp
  · exact Or.inr ⟨collapse s p, old_collapse_of_ne_B s p hp⟩

/-- The distinguished core position has exactly the two occurrence preimages. -/
theorem collapse_eq_s_iff (s : Fin n) (p : Fin (n + 1)) :
    collapse s p = s ↔ p = A s ∨ p = B s := by
  constructor
  · intro hc
    by_cases hp : p = B s
    · exact Or.inr hp
    · left
      calc
        p = old s (collapse s p) := (old_collapse_of_ne_B s p hp).symm
        _ = old s s := congrArg (old s) hc
        _ = A s := old_self s
  · rintro (rfl | rfl)
    · exact collapse_A s
    · exact collapse_B s

/-- Every other core position has exactly its one retained old preimage. -/
theorem collapse_eq_iff_of_ne (s k : Fin n) (hk : k ≠ s) (p : Fin (n + 1)) :
    collapse s p = k ↔ p = old s k := by
  constructor
  · intro hc
    have hp : p ≠ B s := by
      intro he
      have hsk : s = k := by simpa only [he, collapse_B] using hc
      exact hk hsk.symm
    exact (old_collapse_of_ne_B s p hp).symm.trans (congrArg (old s) hc)
  · rintro rfl
    exact collapse_old s k

theorem collapse_fiber_s (s : Fin n) :
    (collapse s) ⁻¹' ({s} : Set (Fin n)) = ({A s, B s} : Set (Fin (n + 1))) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff, collapse_eq_s_iff]

theorem collapse_fiber_of_ne (s k : Fin n) (hk : k ≠ s) :
    (collapse s) ⁻¹' ({k} : Set (Fin n)) = ({old s k} : Set (Fin (n + 1))) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, collapse_eq_iff_of_ne s k hk]

/-- For two increasing child positions, equality after collapse occurs
precisely at the ordered consecutive pair A,B. -/
theorem collapse_eq_iff_of_lt (s : Fin n) (p q : Fin (n + 1)) (hpq : p < q) :
    collapse s p = collapse s q ↔ p = A s ∧ q = B s := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    have hpqv : p.val < q.val := hpq
    rw [collapse_val, collapse_val] at hv
    have hvals : p.val = s.val ∧ q.val = s.val + 1 := by
      split_ifs at hv <;> omega
    exact ⟨Fin.ext hvals.1, Fin.ext hvals.2⟩
  · rintro ⟨rfl, rfl⟩
    rw [collapse_A, collapse_B]

theorem collapse_lt_iff_of_lt (s : Fin n) (p q : Fin (n + 1)) (hpq : p < q) :
    collapse s p < collapse s q ↔ ¬ (p = A s ∧ q = B s) := by
  constructor
  · intro hlt he
    exact (ne_of_lt hlt) ((collapse_eq_iff_of_lt s p q hpq).mpr he)
  · intro hne
    apply lt_of_le_of_ne (collapse_monotone s hpq.le)
    intro he
    exact hne ((collapse_eq_iff_of_lt s p q hpq).mp he)

/-- The sole interval whose two endpoints collapse to the same occurrence. -/
def duplicateInterval (s : Fin n) : BoundaryInterval (n + 1) where
  left := A s
  right := B s
  increasing := A_lt_B s

theorem duplicateInterval_leaves (s : Fin n) : (duplicateInterval s).leaves = 1 := by
  simp only [BoundaryInterval.leaves, duplicateInterval, A_val, B_val, Nat.add_sub_cancel_left]

theorem collapse_endpoints_eq_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    collapse s I.left = collapse s I.right ↔ I = duplicateInterval s := by
  constructor
  · intro he
    obtain ⟨hl, hr⟩ := (collapse_eq_iff_of_lt s I.left I.right I.increasing).mp he
    cases I with
    | mk l r h =>
      change l = A s at hl
      change r = B s at hr
      cases hl
      cases hr
      rfl
  · rintro rfl
    exact (collapse_A s).trans (collapse_B s).symm

theorem collapse_endpoints_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) : collapse s I.left < collapse s I.right := by
  apply lt_of_le_of_ne (collapse_monotone s I.increasing.le)
  intro he
  exact hI ((collapse_endpoints_eq_iff s I).mp he)

/-- Every other interval has a genuine core boundary interval. Its increasing
endpoint proof is derived; callers do not supply distinct collapsed endpoints. -/
def collapseInterval (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) : BoundaryInterval n where
  left := collapse s I.left
  right := collapse s I.right
  increasing := collapse_endpoints_lt s I hI

theorem collapseInterval_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) :
    (collapseInterval s I hI).left = collapse s I.left ∧
    (collapseInterval s I hI).right = collapse s I.right := ⟨rfl, rfl⟩

end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every core position between the collapsed endpoints has an actual lift
inside the child interval. Clamping a global lift to an endpoint changes
neither its collapsed value nor the interval being considered. -/
theorem exists_position_in_interval (s : Fin n) (I : BoundaryInterval (n + 1))
    (k : Fin n) (hk : collapse s I.left ≤ k ∧ k ≤ collapse s I.right) :
    ∃ p : Fin (n + 1), (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p = k := by
  let p := old s k
  have hp : collapse s p = k := collapse_old s k
  by_cases hl : I.left ≤ p
  · by_cases hr : p ≤ I.right
    · exact ⟨p, ⟨hl, hr⟩, hp⟩
    · refine ⟨I.right, ⟨I.increasing.le, le_rfl⟩, le_antisymm ?_ hk.2⟩
      rw [← hp]
      exact collapse_monotone s (le_of_lt (lt_of_not_ge hr))
  · refine ⟨I.left, ⟨le_rfl, I.increasing.le⟩, le_antisymm hk.1 ?_⟩
    rw [← hp]
    exact collapse_monotone s (le_of_lt (lt_of_not_ge hl))

/-- Collapse the actual complete cut set, automatically removing the second
copy of s if both A and B occur. The sole degenerate interval is excluded. -/
def collapseCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (T : BoundaryCutSet I) :
    BoundaryCutSet (collapseInterval s I hI) where
  cuts := T.cuts.image (collapse s)
  left_mem := Finset.mem_image.mpr ⟨I.left, T.left_mem, rfl⟩
  right_mem := Finset.mem_image.mpr ⟨I.right, T.right_mem, rfl⟩
  bounds := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨collapse_monotone s (T.bounds p hp).1,
      collapse_monotone s (T.bounds p hp).2⟩

/-- The local fibre consists of selected physical duplicate occurrences.
Only positions inside the interval may be selected. Nonemptiness records
the core cut at s, and endpoint cuts are mandatory, not optional. -/
def CutFiberCondition (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : Finset (Fin (n + 1))) : Prop :=
  (∀ p ∈ Q, collapse s p = s ∧ I.left ≤ p ∧ p ≤ I.right) ∧
  (Q.Nonempty ↔ s ∈ C.cuts) ∧
  (collapse s I.left = s → I.left ∈ Q) ∧
  (collapse s I.right = s → I.right ∈ Q)

abbrev CutFiber (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :=
  {Q : Finset (Fin (n + 1)) // CutFiberCondition s I hI C Q}

/-- Extract precisely those cuts lying over the distinguished occurrence. -/
def localCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (T : BoundaryCutSet I) :
    CutFiber s I hI (collapseCuts s I hI T) :=
  ⟨T.cuts.filter (fun p => collapse s p = s), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have h := Finset.mem_filter.mp hp
      exact ⟨h.2, T.bounds p h.1⟩
    · constructor
      · rintro ⟨p, hp⟩
        have h := Finset.mem_filter.mp hp
        exact Finset.mem_image.mpr ⟨p, h.1, h.2⟩
      · intro hs
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hs
        exact ⟨p, Finset.mem_filter.mpr ⟨hp, he⟩⟩
    · intro hs
      exact Finset.mem_filter.mpr ⟨T.left_mem, hs⟩
    · intro hs
      exact Finset.mem_filter.mpr ⟨T.right_mem, hs⟩⟩

/-- The inverse is an explicit finite-set formula: take every nonduplicate
preimage of the core cuts inside I, then insert exactly Q. -/
def expandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : BoundaryCutSet I where
  cuts := (Finset.univ.filter (fun p =>
    (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s)) ∪ Q.val
  left_mem := by
    by_cases hs : collapse s I.left = s
    · exact Finset.mem_union_right _ (Q.property.2.2.1 hs)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨⟨le_rfl, I.increasing.le⟩, C.left_mem, hs⟩⟩
  right_mem := by
    by_cases hs : collapse s I.right = s
    · exact Finset.mem_union_right _ (Q.property.2.2.2 hs)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨⟨I.increasing.le, le_rfl⟩, C.right_mem, hs⟩⟩
  bounds := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).2.1
    · exact (Q.property.1 p hp).2

theorem mem_expandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) (p : Fin (n + 1)) :
    p ∈ (expandCuts s I hI C Q).cuts ↔
      ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
        p ∈ Q.val := by
  simp only [expandCuts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

theorem collapse_expandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : collapseCuts s I hI (expandCuts s I hI C Q) = C := by
  apply BoundaryCutSet.ext
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    rcases (mem_expandCuts s I hI C Q p).mp hp with hp | hp
    · exact hp.2.1
    · have hs := (Q.property.1 p hp).1
      rw [hs]
      exact Q.property.2.1.mp ⟨p, hp⟩
  · intro hk
    by_cases hs : k = s
    · have hsc : s ∈ C.cuts := hs ▸ hk
      obtain ⟨p, hp⟩ := Q.property.2.1.mpr hsc
      exact Finset.mem_image.mpr ⟨p,
        (mem_expandCuts s I hI C Q p).mpr (Or.inr hp),
        ((Q.property.1 p hp).1).trans hs.symm⟩
    · obtain ⟨p, hpb, hpc⟩ := exists_position_in_interval s I k (C.bounds k hk)
      apply Finset.mem_image.mpr
      refine ⟨p, (mem_expandCuts s I hI C Q p).mpr (Or.inl ?_), hpc⟩
      exact ⟨hpb, by simpa only [hpc] using hk, by simpa only [hpc] using hs⟩

theorem localCuts_expandCuts_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) :
    (localCuts s I hI (expandCuts s I hI C Q)).val = Q.val := by
  ext p
  change p ∈ (expandCuts s I hI C Q).cuts.filter (fun p => collapse s p = s) ↔ p ∈ Q.val
  constructor
  · intro hp
    obtain ⟨he, hs⟩ := Finset.mem_filter.mp hp
    rcases (mem_expandCuts s I hI C Q p).mp he with he | he
    · exact False.elim (he.2.2 hs)
    · exact he
  · intro hp
    exact Finset.mem_filter.mpr
      ⟨(mem_expandCuts s I hI C Q p).mpr (Or.inr hp), (Q.property.1 p hp).1⟩

theorem expandCuts_collapseCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (T : BoundaryCutSet I) :
    expandCuts s I hI (collapseCuts s I hI T) (localCuts s I hI T) = T := by
  apply BoundaryCutSet.ext
  ext p
  constructor
  · intro hp
    rcases (mem_expandCuts s I hI _ _ p).mp hp with hp | hp
    · obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp.2.1
      have hqold := (collapse_eq_iff_of_ne s (collapse s p) hp.2.2 q).mp he
      have hpold := (collapse_eq_iff_of_ne s (collapse s p) hp.2.2 p).mp rfl
      exact (hqold.trans hpold.symm) ▸ hq
    · exact (Finset.mem_filter.mp hp).1
  · intro hp
    apply (mem_expandCuts s I hI _ _ p).mpr
    by_cases hs : collapse s p = s
    · exact Or.inr (Finset.mem_filter.mpr ⟨hp, hs⟩)
    · exact Or.inl ⟨T.bounds p hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩, hs⟩

/-- Every actual complete child cut set is exactly a core cut set together
with its admissible local subset of A,B. Both inverse identities use the
explicit finite-set formula; no correspondence is supplied as a premise. -/
def cutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) :
    BoundaryCutSet I ≃ Σ C : BoundaryCutSet (collapseInterval s I hI), CutFiber s I hI C where
  toFun T := ⟨collapseCuts s I hI T, localCuts s I hI T⟩
  invFun CQ := expandCuts s I hI CQ.1 CQ.2
  left_inv := expandCuts_collapseCuts s I hI
  right_inv := by
    rintro ⟨C, Q⟩
    have hc := collapse_expandCuts s I hI C Q
    apply Sigma.ext hc
    apply (Subtype.heq_iff_coe_eq (by
      intro U
      change CutFiberCondition s I hI (collapseCuts s I hI (expandCuts s I hI C Q)) U ↔
        CutFiberCondition s I hI C U
      rw [hc])).mpr
    exact localCuts_expandCuts_val s I hI C Q

/-- Reindex the original complete composition domain, including the unary
composition, through the actual cut-set equivalence. -/
def compositionCutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) :
    IntervalComposition I ≃
      Σ C : BoundaryCutSet (collapseInterval s I hI), CutFiber s I hI C :=
  (IntervalComposition.cutSetEquiv I).trans (cutFiberEquiv s I hI)

/-- The local subset contains only the two physical occurrences. -/
theorem cutFiber_subset_pair (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : Q.val ⊆ {A s, B s} := by
  intro p hp
  have h := (collapse_eq_s_iff s p).mp (Q.property.1 p hp).1
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

/-- No core cut at s forces the sole local presentation to be the empty set. -/
theorem cutFiber_empty_iff (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (Q : CutFiber s I hI C) : Q.val = ∅ ↔ s ∉ C.cuts := by
  rw [← Finset.not_nonempty_iff_eq_empty, Q.property.2.1]

/-- All finite sums may now be reindexed by the actual fibres. This local
instance has the same construction as the separate cut-set transform API. -/
local instance cutSetFintype {m : ℕ} [NeZero m] (I : BoundaryInterval m) :
    Fintype (BoundaryCutSet I) :=
  Fintype.ofEquiv (IntervalComposition I) (IntervalComposition.cutSetEquiv I)

theorem sum_cutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (f : BoundaryCutSet I → R) :
    (∑ T : BoundaryCutSet I, f T) =
      ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ∑ Q : CutFiber s I hI C, f (expandCuts s I hI C Q) := by
  calc
    (∑ T : BoundaryCutSet I, f T) =
        ∑ CQ : (Σ C : BoundaryCutSet (collapseInterval s I hI), CutFiber s I hI C),
          f (expandCuts s I hI CQ.1 CQ.2) :=
      Fintype.sum_equiv (cutFiberEquiv s I hI) _ _
        (fun T => congrArg f (expandCuts_collapseCuts s I hI T).symm)
    _ = _ := Fintype.sum_sigma' (fun C Q => f (expandCuts s I hI C Q))

theorem sum_compositionCutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (f : IntervalComposition I → R) :
    (∑ π : IntervalComposition I, f π) =
      ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ∑ Q : CutFiber s I hI C, f (expandCuts s I hI C Q).toComposition := by
  calc
    (∑ π : IntervalComposition I, f π) =
        ∑ T : BoundaryCutSet I, f T.toComposition :=
      Fintype.sum_equiv (IntervalComposition.cutSetEquiv I) _ _
        (fun π => congrArg f π.cutSet_toComposition.symm)
    _ = _ := sum_cutFiber s I hI (fun T => f T.toComposition)

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- All subsets of the two distinct physical occurrences, including empty. -/
theorem cutSubsetPair_cases (s : Fin n) (Q : Finset (Fin (n + 1)))
    (hQ : Q ⊆ {A s, B s}) :
    Q = ∅ ∨ Q = {A s} ∨ Q = {B s} ∨ Q = {A s, B s} := by
  have hm : ∀ p ∈ Q, p = A s ∨ p = B s := by
    intro p hp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hQ hp
  by_cases ha : A s ∈ Q
  · by_cases hb : B s ∈ Q
    · right; right; right
      apply Finset.Subset.antisymm hQ
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · right; left
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨ha, ?_⟩
      intro p hp
      rcases hm p hp with h | h
      · exact h
      · exact False.elim (hb (h ▸ hp))
  · by_cases hb : B s ∈ Q
    · right; right; left
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hb, ?_⟩
      intro p hp
      rcases hm p hp with h | h
      · exact False.elim (ha (h ▸ hp))
      · exact h
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rcases hm p hp with h | h
      · exact ha (h ▸ hp)
      · exact hb (h ▸ hp)

theorem cutFiberCondition_empty (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    CutFiberCondition s I hI C ∅ ↔ s ∉ C.cuts := by
  constructor
  · intro h hs
    exact Finset.not_nonempty_empty (h.2.1.mpr hs)
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      exact False.elim (Finset.notMem_empty p hp)
    · simp only [Finset.not_nonempty_empty, hs, iff_false, not_false_eq_true]
    · intro hl
      have hm := C.left_mem
      change collapse s I.left ∈ C.cuts at hm
      exact False.elim (hs ((congrArg (fun x : Fin n => x ∈ C.cuts) hl).mp hm))
    · intro hr
      have hm := C.right_mem
      change collapse s I.right ∈ C.cuts at hm
      exact False.elim (hs ((congrArg (fun x : Fin n => x ∈ C.cuts) hr).mp hm))

/-- Strictly spanning endpoints impose no local endpoint selection. -/
theorem cutFiberCondition_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q ⊆ {A s, B s} ∧ (Q.Nonempty ↔ s ∈ C.cuts) := by
  constructor
  · intro h
    exact ⟨cutFiber_subset_pair s I hI C ⟨Q, h⟩, h.2.1⟩
  · rintro ⟨hq, hn⟩
    refine ⟨?_, hn, ?_, ?_⟩
    · intro p hp
      have hm := hq hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact ⟨collapse_A s, hL.le, (lt_trans (A_lt_B s) hR).le⟩
      · exact ⟨collapse_B s, (lt_trans hL (A_lt_B s)).le, hR.le⟩
    · intro he
      rcases (collapse_eq_s_iff s I.left).mp he with he | he
      · exact False.elim ((ne_of_lt hL) he)
      · exact False.elim ((ne_of_lt (lt_trans hL (A_lt_B s))) he)
    · intro he
      rcases (collapse_eq_s_iff s I.right).mp he with he | he
      · exact False.elim ((ne_of_gt (lt_trans (A_lt_B s) hR)) he)
      · exact False.elim ((ne_of_gt hR) he)

/-- A spanning core cut at s has exactly the three nonempty subsets. -/
theorem cutFiberCondition_spanning_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q = {A s} ∨ Q = {B s} ∨ Q = {A s, B s} := by
  rw [cutFiberCondition_spanning s I hI C hL hR Q]
  constructor
  · rintro ⟨hq, hn⟩
    rcases cutSubsetPair_cases s Q hq with he | he | he | he
    · exact False.elim ((hn.mpr hs).ne_empty he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  · rintro (rfl | rfl | rfl) <;> simp [hs]

/-- At a left endpoint A, A is mandatory and only the cut at B is optional. -/
theorem cutFiberCondition_start (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q = {A s} ∨ Q = {A s, B s} := by
  have hl : collapse s I.left = s := by rw [hL, collapse_A]
  have hs : s ∈ C.cuts := by
    have hm := C.left_mem
    change collapse s I.left ∈ C.cuts at hm
    exact (congrArg (fun x : Fin n => x ∈ C.cuts) hl).mp hm
  constructor
  · intro h
    have ha : A s ∈ Q := hL ▸ h.2.2.1 hl
    rcases cutSubsetPair_cases s Q (cutFiber_subset_pair s I hI C ⟨Q, h⟩) with he | he | he | he
    · exact False.elim (by simpa only [he, Finset.notMem_empty] using ha)
    · exact Or.inl he
    · have heq : A s = B s := by simpa only [he, Finset.mem_singleton] using ha
      exact False.elim ((ne_of_lt (A_lt_B s)) heq)
    · exact Or.inr he
  · have build : ∀ Q : Finset (Fin (n + 1)), Q ⊆ {A s, B s} → A s ∈ Q →
        CutFiberCondition s I hI C Q := by
      intro Q hq ha
      refine ⟨?_, ⟨fun _ => hs, fun _ => ⟨A s, ha⟩⟩, ?_, ?_⟩
      · intro p hp
        have hm := hq hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact ⟨collapse_A s, hL.le, (lt_trans (A_lt_B s) hR).le⟩
        · exact ⟨collapse_B s, by rw [hL]; exact (A_lt_B s).le, hR.le⟩
      · intro _
        exact hL.symm ▸ ha
      · intro he
        rcases (collapse_eq_s_iff s I.right).mp he with he | he
        · exact False.elim ((ne_of_gt (lt_trans (A_lt_B s) hR)) he)
        · exact False.elim ((ne_of_gt hR) he)
    rintro (rfl | rfl)
    · exact build _ (by simp) (by simp)
    · exact build _ (by simp) (by simp)

/-- At a right endpoint B, B is mandatory and only the cut at A is optional. -/
theorem cutFiberCondition_end (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (Q : Finset (Fin (n + 1))) :
    CutFiberCondition s I hI C Q ↔ Q = {B s} ∨ Q = {A s, B s} := by
  have hr : collapse s I.right = s := by rw [hR, collapse_B]
  have hs : s ∈ C.cuts := by
    have hm := C.right_mem
    change collapse s I.right ∈ C.cuts at hm
    exact (congrArg (fun x : Fin n => x ∈ C.cuts) hr).mp hm
  constructor
  · intro h
    have hb : B s ∈ Q := hR ▸ h.2.2.2 hr
    rcases cutSubsetPair_cases s Q (cutFiber_subset_pair s I hI C ⟨Q, h⟩) with he | he | he | he
    · exact False.elim (by simpa only [he, Finset.notMem_empty] using hb)
    · have heq : B s = A s := by simpa only [he, Finset.mem_singleton] using hb
      exact False.elim ((ne_of_gt (A_lt_B s)) heq)
    · exact Or.inl he
    · exact Or.inr he
  · have build : ∀ Q : Finset (Fin (n + 1)), Q ⊆ {A s, B s} → B s ∈ Q →
        CutFiberCondition s I hI C Q := by
      intro Q hq hb
      refine ⟨?_, ⟨fun _ => hs, fun _ => ⟨B s, hb⟩⟩, ?_, ?_⟩
      · intro p hp
        have hm := hq hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact ⟨collapse_A s, hL.le, by rw [hR]; exact (A_lt_B s).le⟩
        · exact ⟨collapse_B s, (lt_trans hL (A_lt_B s)).le, hR.ge⟩
      · intro he
        rcases (collapse_eq_s_iff s I.left).mp he with he | he
        · exact False.elim ((ne_of_lt hL) he)
        · exact False.elim ((ne_of_lt (lt_trans hL (A_lt_B s))) he)
      · intro _
        exact hR.symm ▸ hb
    rintro (rfl | rfl)
    · exact build _ (by simp) (by simp)
    · exact build _ (by simp) (by simp)

def emptyCutFiber (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : CutFiber s I hI C :=
  ⟨∅, (cutFiberCondition_empty s I hI C).mpr hs⟩

def emptyCutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : PUnit ≃ CutFiber s I hI C :=
  Equiv.ofBijective (fun _ => emptyCutFiber s I hI C hs) ⟨by
    intro x y _
    exact Subsingleton.elim x y, by
    intro Q
    exact ⟨PUnit.unit, Subtype.ext ((cutFiber_empty_iff s I hI C Q).mpr hs).symm⟩⟩

/-- Row zero selects A only, row one B only, and row two both. -/
def spanningRows (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    Fin 3 → CutFiber s I hI C :=
  ![⟨{A s}, (cutFiberCondition_spanning_cut s I hI C hL hR hs _).mpr (Or.inl rfl)⟩,
    ⟨{B s}, (cutFiberCondition_spanning_cut s I hI C hL hR hs _).mpr (Or.inr (Or.inl rfl))⟩,
    ⟨{A s, B s}, (cutFiberCondition_spanning_cut s I hI C hL hR hs _).mpr
      (Or.inr (Or.inr rfl))⟩]

def spanningRowsEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    Fin 3 ≃ CutFiber s I hI C :=
  Equiv.ofBijective (spanningRows s I hI C hL hR hs) ⟨by
    intro i j he
    have ha := congrArg (fun Q : CutFiber s I hI C => A s ∈ Q.val) he
    have hb := congrArg (fun Q : CutFiber s I hI C => B s ∈ Q.val) he
    have hab := ne_of_lt (A_lt_B s)
    have hba := ne_of_gt (A_lt_B s)
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp [spanningRows, hab, hba] at ha hb), by
    intro Q
    rcases (cutFiberCondition_spanning_cut s I hI C hL hR hs Q.val).mp Q.property with h | h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
    · exact ⟨2, Subtype.ext h.symm⟩⟩

/-- At A the two rows differ exactly by the optional cut at B. -/
def startingRows (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) : Fin 2 → CutFiber s I hI C :=
  ![⟨{A s}, (cutFiberCondition_start s I hI C hL hR _).mpr (Or.inl rfl)⟩,
    ⟨{A s, B s}, (cutFiberCondition_start s I hI C hL hR _).mpr (Or.inr rfl)⟩]

def startingRowsEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) : Fin 2 ≃ CutFiber s I hI C :=
  Equiv.ofBijective (startingRows s I hI C hL hR) ⟨by
    intro i j he
    have hb := congrArg (fun Q : CutFiber s I hI C => B s ∈ Q.val) he
    have hba := ne_of_gt (A_lt_B s)
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp [startingRows, hba] at hb), by
    intro Q
    rcases (cutFiberCondition_start s I hI C hL hR Q.val).mp Q.property with h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩⟩

/-- At B the two rows differ exactly by the optional cut at A. -/
def endingRows (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) : Fin 2 → CutFiber s I hI C :=
  ![⟨{B s}, (cutFiberCondition_end s I hI C hL hR _).mpr (Or.inl rfl)⟩,
    ⟨{A s, B s}, (cutFiberCondition_end s I hI C hL hR _).mpr (Or.inr rfl)⟩]

def endingRowsEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) : Fin 2 ≃ CutFiber s I hI C :=
  Equiv.ofBijective (endingRows s I hI C hL hR) ⟨by
    intro i j he
    have ha := congrArg (fun Q : CutFiber s I hI C => A s ∈ Q.val) he
    have hab := ne_of_lt (A_lt_B s)
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp [endingRows, hab] at ha), by
    intro Q
    rcases (cutFiberCondition_end s I hI C hL hR Q.val).mp Q.property with h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩⟩

theorem sum_emptyCutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI)) (hs : s ∉ C.cuts)
    (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (emptyCutFiber s I hI C hs) := by
  have he := (Fintype.sum_equiv (emptyCutFiberEquiv s I hI C hs)
    (fun _ : Unit => f (emptyCutFiber s I hI C hs)) f (fun _ : Unit => rfl)).symm
  simpa using he

theorem sum_spanningRows {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (spanningRows s I hI C hL hR hs 0) +
      f (spanningRows s I hI C hL hR hs 1) + f (spanningRows s I hI C hL hR hs 2) := by
  exact (Fintype.sum_equiv (spanningRowsEquiv s I hI C hL hR hs)
    (fun i => f (spanningRows s I hI C hL hR hs i)) f (fun _ => rfl)).symm.trans
      (Fin.sum_univ_three _)

theorem sum_startingRows {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (startingRows s I hI C hL hR 0) + f (startingRows s I hI C hL hR 1) := by
  exact (Fintype.sum_equiv (startingRowsEquiv s I hI C hL hR)
    (fun i => f (startingRows s I hI C hL hR i)) f (fun _ => rfl)).symm.trans
      (Fin.sum_univ_two _)

theorem sum_endingRows {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : I.right = B s) (f : CutFiber s I hI C → R) :
    (∑ Q, f Q) = f (endingRows s I hI C hL hR 0) + f (endingRows s I hI C hL hR 1) := by
  exact (Fintype.sum_equiv (endingRowsEquiv s I hI C hL hR)
    (fun i => f (endingRows s I hI C hL hR i)) f (fun _ => rfl)).symm.trans
      (Fin.sum_univ_two _)

end
end SM.SoftDuplication


namespace SM.OrderedBoundaryTransport

noncomputable section

universe u
variable {n m : ℕ}

/-- Map both actual endpoints through an arbitrary increasing embedding. -/
def interval (e : Fin n ↪o Fin m) (I : BoundaryInterval n) : BoundaryInterval m where
  left := e I.left
  right := e I.right
  increasing := e.strictMono I.increasing

@[simp] theorem interval_left (e : Fin n ↪o Fin m) (I : BoundaryInterval n) :
    (interval e I).left = e I.left := rfl

@[simp] theorem interval_right (e : Fin n ↪o Fin m) (I : BoundaryInterval n) :
    (interval e I).right = e I.right := rfl

theorem interval_injective (e : Fin n ↪o Fin m) : Function.Injective (interval e) := by
  intro I J h
  cases I with
  | mk l r hi =>
    cases J with
    | mk l' r' hj =>
      have hl : l = l' := e.injective (congrArg BoundaryInterval.left h)
      have hr : r = r' := e.injective (congrArg BoundaryInterval.right h)
      cases hl
      cases hr
      rfl

/-- Map all three positions, preserving their strict order. -/
def triple (e : Fin n ↪o Fin m) (T : IncreasingBoundaryTriple n) :
    IncreasingBoundaryTriple m where
  lower := e T.lower
  middle := e T.middle
  upper := e T.upper
  lower_middle := e.strictMono T.lower_middle
  middle_upper := e.strictMono T.middle_upper

theorem triple_positions (e : Fin n ↪o Fin m) (T : IncreasingBoundaryTriple n) :
    (triple e T).lower = e T.lower ∧
    (triple e T).middle = e T.middle ∧
    (triple e T).upper = e T.upper := ⟨rfl, rfl, rfl⟩

theorem triple_injective (e : Fin n ↪o Fin m) : Function.Injective (triple e) := by
  intro T U h
  cases T with
  | mk l c r hl hc =>
    cases U with
    | mk l' c' r' hl' hc' =>
      have he₁ : l = l' := e.injective (congrArg IncreasingBoundaryTriple.lower h)
      have he₂ : c = c' := e.injective (congrArg IncreasingBoundaryTriple.middle h)
      have he₃ : r = r' := e.injective (congrArg IncreasingBoundaryTriple.upper h)
      cases he₁
      cases he₂
      cases he₃
      rfl

/-- Directly map the cuts, retaining the exact part count and all indices.
This is not a claim that every composition of the image interval is obtained. -/
def composition (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) : IntervalComposition (interval e I) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => e (π.cut k)
  strict := e.strictMono.comp π.strict
  first := congrArg e π.first
  last := congrArg e π.last

@[simp] theorem composition_parts (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) : (composition e π).parts = π.parts := rfl

@[simp] theorem composition_cut (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin (π.parts + 1)) :
    (composition e π).cut k = e (π.cut k) := rfl

theorem composition_endpoints (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) :
    (composition e π).cut 0 = e I.left ∧
    (composition e π).cut (Fin.last π.parts) = e I.right :=
  ⟨congrArg e π.first, congrArg e π.last⟩

@[simp] theorem composition_part (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin π.parts) :
    (composition e π).part k = interval e (π.part k) := rfl

@[simp] theorem composition_nearTriple (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (composition e π).nearTriple k = triple e (π.nearTriple k) := rfl

@[simp] theorem composition_farTriple (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (composition e π).farTriple k = triple e (π.farTriple k) := rfl

/-- The image of the complete cut set, including both endpoints. -/
def cutSet (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (S : BoundaryCutSet I) : BoundaryCutSet (interval e I) where
  cuts := S.cuts.image e
  left_mem := Finset.mem_image.mpr ⟨I.left, S.left_mem, rfl⟩
  right_mem := Finset.mem_image.mpr ⟨I.right, S.right_mem, rfl⟩
  bounds := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨e.monotone (S.bounds x hx).1, e.monotone (S.bounds x hx).2⟩

@[simp] theorem cutSet_cuts (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (S : BoundaryCutSet I) : (cutSet e S).cuts = S.cuts.image e := rfl

theorem cutSet_injective (e : Fin n ↪o Fin m) {I : BoundaryInterval n} :
    Function.Injective (cutSet e (I := I)) := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  intro S T h
  apply BoundaryCutSet.ext
  apply Finset.image_injective e.injective
  exact congrArg BoundaryCutSet.cuts h

/-- Direct cut transport agrees with the actual complete finite cut set. -/
@[simp] theorem composition_cutSet (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) : (composition e π).cutSet = cutSet e π.cutSet := by
  letI : NeZero m := ⟨by have := (e I.left).isLt; omega⟩
  apply BoundaryCutSet.ext
  change Finset.univ.image (fun k => e (π.cut k)) =
    (Finset.univ.image π.cut).image e
  rw [Finset.image_image]
  rfl

theorem composition_injective (e : Fin n ↪o Fin m) {I : BoundaryInterval n} :
    Function.Injective (composition e (I := I)) := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  intro π ρ h
  apply IntervalComposition.cutSet_injective
  apply cutSet_injective e
  have hs := congrArg IntervalComposition.cutSet h
  simpa only [composition_cutSet] using hs

/-- Sorting the image cut set recovers the directly mapped composition. -/
theorem cutSet_toComposition (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (S : BoundaryCutSet I) :
    letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
    letI : NeZero m := ⟨by have := (e I.left).isLt; omega⟩
    (cutSet e S).toComposition = composition e S.toComposition := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  letI : NeZero m := ⟨by have := (e I.left).isLt; omega⟩
  change (cutSet e S).toComposition = composition e S.toComposition
  apply IntervalComposition.cutSet_injective
  rw [BoundaryCutSet.toComposition_cutSet, composition_cutSet,
    BoundaryCutSet.toComposition_cutSet]

variable {R : Type u}

def pullbackTripleArray (e : Fin n ↪o Fin m) (D : TripleArray m R) : TripleArray n R :=
  fun T => D (triple e T)

def pullbackIntervalArray (e : Fin n ↪o Fin m) (X : IntervalArray m R) : IntervalArray n R :=
  fun I => X (interval e I)

variable [CommRing R] [Invertible (2 : R)]

/-- Exact weight transport, with arbitrary arrays and no nonzero factors. -/
theorem nearFarWeight_pullback (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D H : TripleArray m R) :
    (composition e π).nearFarWeight D H =
      π.nearFarWeight (pullbackTripleArray e D) (pullbackTripleArray e H) := by
  rfl

/-- Only the actual near/far factors of this composition need agree. -/
theorem nearFarWeight_transport (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D₀ H₀ : TripleArray n R) (D₁ H₁ : TripleArray m R)
    (hD : ∀ k : Fin (π.parts - 1), D₁ (triple e (π.nearTriple k)) = D₀ (π.nearTriple k))
    (hH : ∀ k : Fin (π.parts - 1), H₁ (triple e (π.farTriple k)) = H₀ (π.farTriple k)) :
    (composition e π).nearFarWeight D₁ H₁ = π.nearFarWeight D₀ H₀ := by
  change (∏ k : Fin (π.parts - 1),
    (D₁ (triple e (π.nearTriple k)) - H₁ (triple e (π.farTriple k))) * ⅟ (2 : R)) =
      ∏ k : Fin (π.parts - 1), (D₀ (π.nearTriple k) - H₀ (π.farTriple k)) * ⅟ (2 : R)
  apply Finset.prod_congr rfl
  intro k hk
  rw [hD k, hH k]

/-- The child product uses the actual mapped child intervals. -/
theorem childProduct_transport (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (X₀ : IntervalArray n R) (X₁ : IntervalArray m R)
    (hX : ∀ k : Fin π.parts, X₁ (interval e (π.part k)) = X₀ (π.part k)) :
    (∏ k : Fin (composition e π).parts, X₁ ((composition e π).part k)) =
      ∏ k : Fin π.parts, X₀ (π.part k) := by
  change (∏ k : Fin π.parts, X₁ (interval e (π.part k))) =
    ∏ k : Fin π.parts, X₀ (π.part k)
  apply Finset.prod_congr rfl
  intro k hk
  exact hX k

/-- The complete raw transform summand, including its entire child product.
Unary weights remain empty products, and zero factors need not be cancelled. -/
theorem summand_transport (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D₀ H₀ : TripleArray n R) (D₁ H₁ : TripleArray m R)
    (X₀ : IntervalArray n R) (X₁ : IntervalArray m R)
    (hD : ∀ k : Fin (π.parts - 1), D₁ (triple e (π.nearTriple k)) = D₀ (π.nearTriple k))
    (hH : ∀ k : Fin (π.parts - 1), H₁ (triple e (π.farTriple k)) = H₀ (π.farTriple k))
    (hX : ∀ k : Fin π.parts, X₁ (interval e (π.part k)) = X₀ (π.part k)) :
    (composition e π).nearFarWeight D₁ H₁ *
        (∏ k : Fin (composition e π).parts, X₁ ((composition e π).part k)) =
      π.nearFarWeight D₀ H₀ * ∏ k : Fin π.parts, X₀ (π.part k) := by
  rw [nearFarWeight_transport e π D₀ H₀ D₁ H₁ hD hH,
    childProduct_transport e π X₀ X₁ hX]

/-- Unconditional formulation using the exact pointwise pullback arrays. -/
theorem summand_pullback (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D H : TripleArray m R) (X : IntervalArray m R) :
    (composition e π).nearFarWeight D H *
        (∏ k : Fin (composition e π).parts, X ((composition e π).part k)) =
      π.nearFarWeight (pullbackTripleArray e D) (pullbackTripleArray e H) *
        ∏ k : Fin π.parts, pullbackIntervalArray e X (π.part k) := by
  apply summand_transport e π
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rfl

end

end SM.OrderedBoundaryTransport


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Exact membership in an increasing image of a complete cut set. -/
theorem cut_mem_ordered_image {m : ℕ} (e : Fin n ↪o Fin m)
    {J : BoundaryInterval n} (C : BoundaryCutSet J) (k : Fin n) :
    e k ∈ C.cuts.image e ↔ k ∈ C.cuts := by
  constructor
  · intro h
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp h
    exact e.injective he ▸ hl
  · intro h
    exact Finset.mem_image.mpr ⟨k, h, rfl⟩

/-- Consecutiveness is preserved and reflected by an actual cut-set image. -/
theorem consecutive_ordered_image_iff {m : ℕ} [NeZero m]
    (e : Fin n ↪o Fin m) {J : BoundaryInterval n} {I : BoundaryInterval m}
    (C : BoundaryCutSet J) (T : BoundaryCutSet I) (hcuts : T.cuts = C.cuts.image e)
    (K : BoundaryInterval n) :
    T.Consecutive (OrderedBoundaryTransport.interval e K) ↔ C.Consecutive K := by
  constructor
  · rintro ⟨hl, hr, hn⟩
    have hcl : K.left ∈ C.cuts := (cut_mem_ordered_image e C K.left).mp (by
      rw [← hcuts]; exact hl)
    have hcr : K.right ∈ C.cuts := (cut_mem_ordered_image e C K.right).mp (by
      rw [← hcuts]; exact hr)
    refine ⟨hcl, hcr, ?_⟩
    intro k hk hb
    have hm : e k ∈ T.cuts := by
      rw [hcuts]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    exact hn (e k) hm ⟨e.strictMono hb.1, e.strictMono hb.2⟩
  · rintro ⟨hl, hr, hn⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hcuts]
      exact Finset.mem_image.mpr ⟨K.left, hl, rfl⟩
    · rw [hcuts]
      exact Finset.mem_image.mpr ⟨K.right, hr, rfl⟩
    · intro p hp hb
      rw [hcuts] at hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      exact hn k hk ⟨e.strictMono.lt_iff_lt.mp hb.1, e.strictMono.lt_iff_lt.mp hb.2⟩

/-- Every child of the image cut set comes from an actual core child. -/
theorem consecutive_ordered_image_exhaust {m : ℕ} [NeZero m]
    (e : Fin n ↪o Fin m) {J : BoundaryInterval n} {I : BoundaryInterval m}
    (C : BoundaryCutSet J) (T : BoundaryCutSet I) (hcuts : T.cuts = C.cuts.image e)
    (K : BoundaryInterval m) (hK : T.Consecutive K) :
    ∃ L : BoundaryInterval n, C.Consecutive L ∧ OrderedBoundaryTransport.interval e L = K := by
  have hl : K.left ∈ C.cuts.image e := by rw [← hcuts]; exact hK.1
  have hr : K.right ∈ C.cuts.image e := by rw [← hcuts]; exact hK.2.1
  obtain ⟨l, hlc, hel⟩ := Finset.mem_image.mp hl
  obtain ⟨r, hrc, her⟩ := Finset.mem_image.mp hr
  have hlr : l < r := e.strictMono.lt_iff_lt.mp (by rw [hel, her]; exact K.increasing)
  let L : BoundaryInterval n := ⟨l, r, hlr⟩
  have he : OrderedBoundaryTransport.interval e L = K :=
    BoundaryInterval.eq_of_endpoints hel her
  refine ⟨L, (consecutive_ordered_image_iff e C T hcuts L).mp ?_, he⟩
  rw [he]
  exact hK

def consecutiveOrderedImageEquiv {m : ℕ} [NeZero m]
    (e : Fin n ↪o Fin m) {J : BoundaryInterval n} {I : BoundaryInterval m}
    (C : BoundaryCutSet J) (T : BoundaryCutSet I) (hcuts : T.cuts = C.cuts.image e) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {L : BoundaryInterval m // T.Consecutive L} :=
  Equiv.ofBijective (fun K => ⟨OrderedBoundaryTransport.interval e K.val,
    (consecutive_ordered_image_iff e C T hcuts K.val).mpr K.property⟩) ⟨by
    intro K L he
    apply Subtype.ext
    exact OrderedBoundaryTransport.interval_injective e (congrArg Subtype.val he), by
    intro L
    obtain ⟨K, hK, he⟩ := consecutive_ordered_image_exhaust e C T hcuts L.val L.property
    exact ⟨⟨K, hK⟩, Subtype.ext he⟩⟩

def startingOldEmbedding (s : Fin n) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (old s) (old_strictMono s)

/-- The increasing section which retains the core endpoint at B instead of A. -/
def startingTailEmbedding (s : Fin n) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono ((A s).succAbove) (Fin.strictMono_succAbove (A s))

@[simp] theorem startingTail_self (s : Fin n) : startingTailEmbedding s s = B s :=
  Fin.succAbove_castSucc_self s

@[simp] theorem collapse_startingTail (s k : Fin n) :
    collapse s (startingTailEmbedding s k) = k := Fin.predAbove_succAbove s k

theorem startingTail_eq_old (s k : Fin n) (hk : k ≠ s) :
    startingTailEmbedding s k = old s k :=
  (collapse_eq_iff_of_ne s k hk _).mp (collapse_startingTail s k)

theorem starting_B_lt_old (s k : Fin n) (hk : s < k) : B s < old s k := by
  have h := (startingTailEmbedding s).strictMono hk
  simpa only [startingTail_self, startingTail_eq_old s k (ne_of_gt hk)] using h

def startingCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (i : Fin 2) : BoundaryCutSet I :=
  expandCuts s I hI C (startingRows s I hI C hL hR i)

theorem starting_core_left (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) :
    (collapseInterval s I hI).left = s := by
  change collapse s I.left = s
  rw [hL, collapse_A]

theorem starting_core_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) : s ∈ C.cuts := by
  have hm := C.left_mem
  exact (congrArg (fun x : Fin n => x ∈ C.cuts) (starting_core_left s I hI hL)).mp hm

theorem starting_old_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ old s k ∧ old s k ≤ I.right := by
  have hb := C.bounds k hk
  have hsk : s ≤ k := by simpa only [starting_core_left s I hI hL] using hb.1
  constructor
  · rw [hL, ← old_self s]
    exact (old_strictMono s).monotone hsk
  · have hright := (old_strictMono s).monotone hb.2
    change old s k ≤ old s (collapse s I.right) at hright
    rwa [old_collapse_of_ne_B s I.right (ne_of_gt hR)] at hright

/-- Row zero is exactly the old-position image, with no cut at B. -/
theorem startingCutSet_zero_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 0).cuts = C.cuts.image (old s) := by
  ext p
  have hm := mem_expandCuts s I hI C (startingRows s I hI C hL hR 0) p
  change p ∈ (startingCutSet s I hI C hL hR 0).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (startingRows s I hI C hL hR 0).val at hm
  simp only [startingRows, Matrix.cons_val_zero, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1, he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, starting_core_cut s I hI C hL, old_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, old_self])
    · left
      exact ⟨starting_old_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_old] using hk, by simpa only [collapse_old] using hks⟩

theorem startingCutSet_one_insert_B (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).cuts =
      insert (B s) (startingCutSet s I hI C hL hR 0).cuts := by
  ext p
  simp only [startingCutSet, mem_expandCuts, startingRows, Matrix.cons_val_zero,
    Matrix.cons_val_one, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem starting_sections_cut_image (s : Fin n) (C : Finset (Fin n)) (hs : s ∈ C) :
    insert (B s) (C.image (old s)) = insert (A s) (C.image (startingTailEmbedding s)) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, startingTail_self s⟩)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      by_cases hks : k = s
      · exact Finset.mem_insert.mpr (Or.inl (by rw [hks, old_self]))
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨k, hk, startingTail_eq_old s k hks⟩)
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, old_self s⟩)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      by_cases hks : k = s
      · exact Finset.mem_insert.mpr (Or.inl (by rw [hks, startingTail_self]))
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨k, hk, (startingTail_eq_old s k hks).symm⟩)

/-- Row one is a leading A followed by the entire core cut list based at B. -/
theorem startingCutSet_one_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).cuts =
      insert (A s) (C.cuts.image (startingTailEmbedding s)) := by
  rw [startingCutSet_one_insert_B, startingCutSet_zero_cuts]
  exact starting_sections_cut_image s C.cuts (starting_core_cut s I hI C hL)

/-- The actual first child is defined even when the core composition is unary. -/
def startingFirstChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    BoundaryInterval n := C.toComposition.part ⟨0, C.toComposition.parts_pos⟩

theorem startingFirstChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    C.Consecutive (startingFirstChild s I hI C) := by
  simpa only [startingFirstChild, BoundaryCutSet.toComposition_cutSet] using
    C.toComposition.part_consecutive ⟨0, C.toComposition.parts_pos⟩

theorem startingFirstChild_left (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) : (startingFirstChild s I hI C).left = s := by
  change C.toComposition.cut 0 = s
  rw [C.toComposition.first, starting_core_left s I hI hL]

theorem startingFirstChild_right (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) :
    s < (startingFirstChild s I hI C).right ∧ (startingFirstChild s I hI C).right ∈ C.cuts := by
  refine ⟨?_, (startingFirstChild_consecutive s I hI C).2.1⟩
  exact lt_of_eq_of_lt (startingFirstChild_left s I hI C hL).symm
    (startingFirstChild s I hI C).increasing

theorem startingFirstChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : K.left = s) :
    K = startingFirstChild s I hI C :=
  C.consecutive_eq_of_left hK (startingFirstChild_consecutive s I hI C)
    (hk.trans (startingFirstChild_left s I hI C hL).symm)

theorem startingFirstChild_right_le (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (k : Fin n) (hk : k ∈ C.cuts) (hsk : s < k) :
    (startingFirstChild s I hI C).right ≤ k := by
  apply le_of_not_gt
  intro hlt
  exact (startingFirstChild_consecutive s I hI C).2.2 k hk
    ⟨by rw [startingFirstChild_left s I hI C hL]; exact hsk, hlt⟩

def startingChildrenZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {J : BoundaryInterval (n + 1) // (startingCutSet s I hI C hL hR 0).Consecutive J} :=
  consecutiveOrderedImageEquiv (startingOldEmbedding s) C (startingCutSet s I hI C hL hR 0)
    (startingCutSet_zero_cuts s I hI C hL hR)

theorem starting_tail_cut_gt_A (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (k : Fin n) (hk : k ∈ C.cuts) : A s < startingTailEmbedding s k := by
  have hsk : s ≤ k := by
    simpa only [starting_core_left s I hI hL] using (C.bounds k hk).1
  have hb : B s ≤ startingTailEmbedding s k := by
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).monotone hsk
  exact lt_of_lt_of_le (A_lt_B s) hb

/-- Every core child remains consecutive after renaming its first endpoint
to B and adjoining the leading cut A. -/
theorem starting_one_mapped_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (K : BoundaryInterval n) (hK : C.Consecutive K) :
    (startingCutSet s I hI C hL hR 1).Consecutive
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) := by
  let U := OrderedBoundaryTransport.cutSet (startingTailEmbedding s) C
  have hU : U.Consecutive (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) :=
    (consecutive_ordered_image_iff (startingTailEmbedding s) C U rfl K).mpr hK
  refine ⟨?_, ?_, ?_⟩
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K.left, hK.1, rfl⟩)
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨K.right, hK.2.1, rfl⟩)
  · intro p hp hb
    rw [startingCutSet_one_cuts] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact lt_asymm (starting_tail_cut_gt_A s I hI C hL K.left hK.1) hb.1
    · exact hU.2.2 p hp hb

/-- The only extra child in row one is the actual consecutive interval A,B. -/
theorem starting_one_duplicate_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).Consecutive (duplicateInterval s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_self _ _
  · rw [startingCutSet_one_cuts]
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨s, starting_core_cut s I hI C hL, startingTail_self s⟩)
  · intro p _ hb
    have hl : s.val < p.val := hb.1
    have hr : p.val < s.val + 1 := hb.2
    omega

/-- Exhaustive classification of actual row-one consecutive children. -/
theorem starting_one_consecutive_iff (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (J : BoundaryInterval (n + 1)) :
    (startingCutSet s I hI C hL hR 1).Consecutive J ↔
      J = duplicateInterval s ∨ ∃ K : BoundaryInterval n,
        C.Consecutive K ∧ OrderedBoundaryTransport.interval (startingTailEmbedding s) K = J := by
  constructor
  · intro hJ
    by_cases hja : J.left = A s
    · exact Or.inl ((startingCutSet s I hI C hL hR 1).consecutive_eq_of_left hJ
        (starting_one_duplicate_consecutive s I hI C hL hR) hja)
    · right
      have hl : J.left ∈ C.cuts.image (startingTailEmbedding s) := by
        have hm := hJ.1
        rw [startingCutSet_one_cuts] at hm
        exact (Finset.mem_insert.mp hm).resolve_left hja
      have har : A s < J.right := by
        have hb := ((startingCutSet s I hI C hL hR 1).bounds J.left hJ.1).1
        have hal : A s ≤ J.left := by simpa only [hL] using hb
        exact lt_of_le_of_lt hal J.increasing
      have hr : J.right ∈ C.cuts.image (startingTailEmbedding s) := by
        have hm := hJ.2.1
        rw [startingCutSet_one_cuts] at hm
        exact (Finset.mem_insert.mp hm).resolve_left (ne_of_gt har)
      let U := OrderedBoundaryTransport.cutSet (startingTailEmbedding s) C
      have hU : U.Consecutive J := by
        refine ⟨hl, hr, ?_⟩
        intro p hp hb
        have ht : p ∈ (startingCutSet s I hI C hL hR 1).cuts := by
          rw [startingCutSet_one_cuts]
          exact Finset.mem_insert_of_mem hp
        exact hJ.2.2 p ht hb
      exact consecutive_ordered_image_exhaust (startingTailEmbedding s) C U rfl J hU
  · rintro (rfl | ⟨K, hK, rfl⟩)
    · exact starting_one_duplicate_consecutive s I hI C hL hR
    · exact starting_one_mapped_consecutive s I hI C hL hR K hK

def startingChildOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    Unit ⊕ {K : BoundaryInterval n // C.Consecutive K} →
      {J : BoundaryInterval (n + 1) // (startingCutSet s I hI C hL hR 1).Consecutive J} :=
  Sum.elim (fun _ : Unit => ⟨duplicateInterval s, starting_one_duplicate_consecutive s I hI C hL hR⟩)
    (fun K => ⟨OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val,
      starting_one_mapped_consecutive s I hI C hL hR K.val K.property⟩)

/-- Actual child-domain bijection: one singleton plus every core child. -/
def startingChildrenOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (Unit ⊕ {K : BoundaryInterval n // C.Consecutive K}) ≃
      {J : BoundaryInterval (n + 1) // (startingCutSet s I hI C hL hR 1).Consecutive J} :=
  Equiv.ofBijective (startingChildOneMap s I hI C hL hR) ⟨by
    intro a b he
    cases a with
    | inl u =>
      cases b with
      | inl v => cases u; cases v; rfl
      | inr K =>
        have hx : A s = startingTailEmbedding s K.val.left :=
          congrArg (fun J => J.val.left) he
        exact False.elim ((ne_of_lt (starting_tail_cut_gt_A s I hI C hL K.val.left K.property.1)) hx)
    | inr K =>
      cases b with
      | inl u =>
        have hx : startingTailEmbedding s K.val.left = A s :=
          congrArg (fun J => J.val.left) he
        exact False.elim ((ne_of_gt (starting_tail_cut_gt_A s I hI C hL K.val.left K.property.1)) hx)
      | inr L =>
        have hval : K.val = L.val := OrderedBoundaryTransport.interval_injective
          (startingTailEmbedding s) (congrArg Subtype.val he)
        exact congrArg Sum.inr (Subtype.ext hval), by
    intro J
    rcases (starting_one_consecutive_iff s I hI C hL hR J.val).mp J.property with h | ⟨K, hK, he⟩
    · exact ⟨Sum.inl (), Subtype.ext h.symm⟩
    · exact ⟨Sum.inr ⟨K, hK⟩, Subtype.ext he⟩⟩

/-- The row-zero first child really spans both duplicate occurrences. -/
theorem starting_first_zero_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)).left = A s ∧
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)).right =
      old s (startingFirstChild s I hI C).right ∧
    B s < old s (startingFirstChild s I hI C).right := by
  refine ⟨?_, rfl, starting_B_lt_old s _ (startingFirstChild_right s I hI C hL).1⟩
  change old s (startingFirstChild s I hI C).left = A s
  rw [startingFirstChild_left s I hI C hL, old_self]

/-- After the singleton, the same first core child starts at B. -/
theorem starting_first_one_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) :
    (OrderedBoundaryTransport.interval (startingTailEmbedding s) (startingFirstChild s I hI C)).left = B s ∧
    (OrderedBoundaryTransport.interval (startingTailEmbedding s) (startingFirstChild s I hI C)).right =
      old s (startingFirstChild s I hI C).right := by
  constructor
  · change startingTailEmbedding s (startingFirstChild s I hI C).left = B s
    rw [startingFirstChild_left s I hI C hL, startingTail_self]
  · exact startingTail_eq_old s _ (ne_of_gt (startingFirstChild_right s I hI C hL).1)

theorem starting_otherChild_left_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ startingFirstChild s I hI C) : s < K.left := by
  have hle : s ≤ K.left := by
    simpa only [starting_core_left s I hI hL] using (C.bounds K.left hK.1).1
  apply lt_of_le_of_ne hle
  intro he
  exact hne (startingFirstChild_unique s I hI C hL K hK he.symm)

/-- Every other child interval is literally the same in both presentations. -/
theorem starting_otherChild_map_eq (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ startingFirstChild s I hI C) :
    OrderedBoundaryTransport.interval (startingTailEmbedding s) K =
      OrderedBoundaryTransport.interval (startingOldEmbedding s) K := by
  have hl := starting_otherChild_left_gt s I hI C hL K hK hne
  apply BoundaryInterval.eq_of_endpoints
  · exact startingTail_eq_old s K.left (ne_of_gt hl)
  · exact startingTail_eq_old s K.right (ne_of_gt (lt_trans hl K.increasing))

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Collapse remains strictly below s before A. -/
theorem collapse_lt_distinguished (s : Fin n) (p : Fin (n + 1)) (hp : p < A s) :
    collapse s p < s := by
  have h := (collapse_lt_iff_of_lt s p (A s) hp).mpr
    (fun he => (ne_of_lt hp) he.1)
  simpa only [collapse_A] using h

/-- Collapse remains strictly above s after B. -/
theorem distinguished_lt_collapse (s : Fin n) (p : Fin (n + 1)) (hp : B s < p) :
    s < collapse s p := by
  have h := (collapse_lt_iff_of_lt s (B s) p hp).mpr
    (fun he => (ne_of_lt (A_lt_B s)) he.1.symm)
  simpa only [collapse_B] using h

/-- Literal occurrence membership of both duplicated positions in a triple. -/
def tripleContainsBoth (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) : Prop :=
  (T.lower = A s ∨ T.middle = A s ∨ T.upper = A s) ∧
  (T.lower = B s ∨ T.middle = B s ∨ T.upper = B s)

theorem triple_exception_disjoint (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) :
    ¬ ((T.middle = A s ∧ T.upper = B s) ∧ (T.lower = A s ∧ T.middle = B s)) := by
  rintro ⟨hu, hl⟩
  exact (ne_of_lt (A_lt_B s)) (hu.1.symm.trans hl.2)

/-- Consecutiveness rules out A and B as lower/upper with a middle between
them. The two adjacent exceptional placements are therefore exhaustive. -/
theorem triple_contains_both_iff (s : Fin n) (T : IncreasingBoundaryTriple (n + 1)) :
    tripleContainsBoth s T ↔
      (T.middle = A s ∧ T.upper = B s) ∨ (T.lower = A s ∧ T.middle = B s) := by
  constructor
  · rintro ⟨hA, hB⟩
    have hlow : T.lower.val < T.middle.val := T.lower_middle
    have hupp : T.middle.val < T.upper.val := T.middle_upper
    rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
      first
      | exact Or.inl ⟨hA, hB⟩
      | exact Or.inr ⟨hA, hB⟩
      | have ha := congrArg Fin.val hA
        have hb := congrArg Fin.val hB
        simp only [A_val, B_val] at ha hb
        omega
  · rintro (⟨hm, hu⟩ | ⟨hl, hm⟩)
    · exact ⟨Or.inr (Or.inl hm), Or.inr (Or.inr hu)⟩
    · exact ⟨Or.inl hl, Or.inr (Or.inl hm)⟩

/-- The plain case has strictly increasing collapsed positions, proved from
the exact sole equality exception of the collapse map. -/
def collapseTriple (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ tripleContainsBoth s T) : IncreasingBoundaryTriple n where
  lower := collapse s T.lower
  middle := collapse s T.middle
  upper := collapse s T.upper
  lower_middle := (collapse_lt_iff_of_lt s T.lower T.middle T.lower_middle).mpr
    (fun hl => hplain ((triple_contains_both_iff s T).mpr (Or.inr hl)))
  middle_upper := (collapse_lt_iff_of_lt s T.middle T.upper T.middle_upper).mpr
    (fun hu => hplain ((triple_contains_both_iff s T).mpr (Or.inl hu)))

theorem collapseTriple_positions (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hplain : ¬ tripleContainsBoth s T) :
    (collapseTriple s T hplain).lower = collapse s T.lower ∧
    (collapseTriple s T hplain).middle = collapse s T.middle ∧
    (collapseTriple s T hplain).upper = collapse s T.upper := ⟨rfl, rfl, rfl⟩

def oldTriple (s : Fin n) (T : IncreasingBoundaryTriple n) : IncreasingBoundaryTriple (n + 1) where
  lower := old s T.lower
  middle := old s T.middle
  upper := old s T.upper
  lower_middle := old_strictMono s T.lower_middle
  middle_upper := old_strictMono s T.middle_upper

theorem oldTriple_plain (s : Fin n) (T : IncreasingBoundaryTriple n) :
    ¬ tripleContainsBoth s (oldTriple s T) := by
  intro h
  rcases (triple_contains_both_iff s (oldTriple s T)).mp h with hu | hl
  · exact old_ne_B s T.upper hu.2
  · exact old_ne_B s T.middle hl.2

theorem triple_ext {T U : IncreasingBoundaryTriple n}
    (hl : T.lower = U.lower) (hm : T.middle = U.middle) (hu : T.upper = U.upper) : T = U := by
  cases T with
  | mk l m u h1 h2 =>
    cases U with
    | mk l' m' u' h1' h2' =>
      change l = l' at hl
      change m = m' at hm
      change u = u' at hu
      cases hl
      cases hm
      cases hu
      rfl

theorem collapseTriple_oldTriple (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hplain : ¬ tripleContainsBoth s (oldTriple s T)) :
    collapseTriple s (oldTriple s T) hplain = T := by
  apply triple_ext
  · exact collapse_old s T.lower
  · exact collapse_old s T.middle
  · exact collapse_old s T.upper

/-- The complete source pullback/exceptional array prescription. The two
exceptional pairs are disjoint; every other triple has a proved core triple. -/
def tripleLift {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R) :
    TripleArray (n + 1) R := fun T =>
  if hu : T.middle = A s ∧ T.upper = B s then t (collapse s T.lower)
  else if hl : T.lower = A s ∧ T.middle = B s then t (collapse s T.upper)
  else H0 (collapseTriple s T (fun h =>
    ((triple_contains_both_iff s T).mp h).elim hu hl))

theorem tripleLift_upper {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hu : T.middle = A s ∧ T.upper = B s) :
    tripleLift s H0 t T = t (collapse s T.lower) := by
  simp only [tripleLift, dif_pos hu]

theorem tripleLift_lower {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hl : T.lower = A s ∧ T.middle = B s) :
    tripleLift s H0 t T = t (collapse s T.upper) := by
  have hu : ¬ (T.middle = A s ∧ T.upper = B s) :=
    fun h => triple_exception_disjoint s T ⟨h, hl⟩
  simp only [tripleLift, dif_neg hu, dif_pos hl]

theorem tripleLift_plain {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple (n + 1)) (hplain : ¬ tripleContainsBoth s T) :
    tripleLift s H0 t T = H0 (collapseTriple s T hplain) := by
  have hu : ¬ (T.middle = A s ∧ T.upper = B s) :=
    fun h => hplain ((triple_contains_both_iff s T).mpr (Or.inl h))
  have hl : ¬ (T.lower = A s ∧ T.middle = B s) :=
    fun h => hplain ((triple_contains_both_iff s T).mpr (Or.inr h))
  simp only [tripleLift, dif_neg hu, dif_neg hl]

theorem tripleLift_oldTriple {R : Type*} (s : Fin n) (H0 : TripleArray n R) (t : Fin n → R)
    (T : IncreasingBoundaryTriple n) : tripleLift s H0 t (oldTriple s T) = H0 T := by
  rw [tripleLift_plain s H0 t (oldTriple s T) (oldTriple_plain s T), collapseTriple_oldTriple]

theorem upper_exception_argument_lt (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hu : T.middle = A s ∧ T.upper = B s) : collapse s T.lower < s :=
  collapse_lt_distinguished s T.lower (lt_of_lt_of_eq T.lower_middle hu.1)

theorem lower_exception_argument_gt (s : Fin n) (T : IncreasingBoundaryTriple (n + 1))
    (hl : T.lower = A s ∧ T.middle = B s) : s < collapse s T.upper := by
  apply distinguished_lt_collapse s T.upper
  simpa only [hl.2] using T.middle_upper

/-- The source auxiliary core near array; it is not asserted geometric. -/
def coreNear (s : Fin n) (t : Fin n → ℚ) : TripleArray n ℚ := fun T =>
  if T.middle = s then t T.lower else 0

theorem coreNear_at_middle (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n)
    (hm : T.middle = s) : coreNear s t T = t T.lower := by
  simp only [coreNear, if_pos hm]

theorem coreNear_off_middle (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n)
    (hm : T.middle ≠ s) : coreNear s t T = 0 := by
  simp only [coreNear, if_neg hm]

theorem coreNear_argument_lt (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hm : T.middle = s) : T.lower < s := lt_of_lt_of_eq T.lower_middle hm

/-- The auxiliary parent near array uses the same exact exceptional t-data
and otherwise pulls back coreNear. -/
def parentNear (s : Fin n) (t : Fin n → ℚ) : TripleArray (n + 1) ℚ :=
  tripleLift s (coreNear s t) t

theorem parentNear_oldTriple (s : Fin n) (t : Fin n → ℚ) (T : IncreasingBoundaryTriple n) :
    parentNear s t (oldTriple s T) = coreNear s t T := tripleLift_oldTriple s _ t T

/-- Both occurrences lie in the closed interval. Since A<B, the other two
endpoint inequalities follow automatically. -/
def intervalContainsBoth (s : Fin n) (I : BoundaryInterval (n + 1)) : Prop :=
  I.left ≤ A s ∧ B s ≤ I.right

theorem intervalContainsBoth_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    intervalContainsBoth s I ↔
      (I.left ≤ A s ∧ A s ≤ I.right) ∧ (I.left ≤ B s ∧ B s ≤ I.right) := by
  constructor
  · intro h
    exact ⟨⟨h.1, le_trans (A_lt_B s).le h.2⟩,
      ⟨le_trans h.1 (A_lt_B s).le, h.2⟩⟩
  · intro h
    exact ⟨h.1.1, h.2.2⟩

theorem interval_eq_duplicate (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : I.right = B s) : I = duplicateInterval s := by
  apply (collapse_endpoints_eq_iff s I).mp
  rw [hl, hr, collapse_A, collapse_B]

/-- Exactly the five source rows, with strict exterior endpoints in the
three nonsingleton cases containing both occurrences. -/
theorem interval_five_cases (s : Fin n) (I : BoundaryInterval (n + 1)) :
    (¬ intervalContainsBoth s I) ∨ I = duplicateInterval s ∨
    (I.left = A s ∧ B s < I.right) ∨ (I.left < A s ∧ I.right = B s) ∨
    (I.left < A s ∧ B s < I.right) := by
  by_cases h : intervalContainsBoth s I
  · rcases lt_or_eq_of_le h.1 with hl | hl
    · rcases lt_or_eq_of_le h.2 with hr | hr
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hl, hr⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, hr.symm⟩)))
    · rcases lt_or_eq_of_le h.2 with hr | hr
      · exact Or.inr (Or.inr (Or.inl ⟨hl, hr⟩))
      · exact Or.inr (Or.inl (interval_eq_duplicate s I hl hr.symm))
  · exact Or.inl h

theorem not_duplicate_of_not_contains (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : ¬ intervalContainsBoth s I) : I ≠ duplicateInterval s := by
  rintro rfl
  exact h ⟨le_rfl, le_rfl⟩

theorem not_duplicate_of_right_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : B s < I.right) : I ≠ duplicateInterval s := by
  intro he
  have hb : B s < B s := by simpa only [he, duplicateInterval] using h
  exact (lt_irrefl _) hb

theorem not_duplicate_of_left_lt (s : Fin n) (I : BoundaryInterval (n + 1))
    (h : I.left < A s) : I ≠ duplicateInterval s := by
  intro he
  have ha : A s < A s := by simpa only [he, duplicateInterval] using h
  exact (lt_irrefl _) ha

theorem start_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right) :
    collapse s I.left = s ∧ s < collapse s I.right :=
  ⟨by rw [hl, collapse_A], distinguished_lt_collapse s I.right hr⟩

theorem end_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s) :
    collapse s I.left < s ∧ collapse s I.right = s :=
  ⟨collapse_lt_distinguished s I.left hl, by rw [hr, collapse_B]⟩

theorem span_collapsed_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : B s < I.right) :
    collapse s I.left < s ∧ s < collapse s I.right :=
  ⟨collapse_lt_distinguished s I.left hl, distinguished_lt_collapse s I.right hr⟩

/-- The proposed five-row ordinary array, defined on every child interval.
The duplicate interval is handled before forming any collapsed interval.
No recurrence or inverse-solution assertion is built into this definition. -/
def ordinaryLift (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) : IntervalArray (n + 1) ℚ := fun I =>
  if hdup : I = duplicateInterval s then 1
  else
    let J := collapseInterval s I hdup
    if intervalContainsBoth s I then
      if I.left = A s then ((etaPlus - t (collapse s I.right)) / 2) * b0 J
      else if I.right = B s then ((etaMinus - t (collapse s I.left)) / 2) * b0 J
      else ((etaMinus + etaPlus) / 2) * b0 J
    else b0 J

theorem ordinaryLift_duplicate (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) : ordinaryLift s etaMinus etaPlus t b0 (duplicateInterval s) = 1 := by
  simp [ordinaryLift]

theorem ordinaryLift_plain (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (h : ¬ intervalContainsBoth s I) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      b0 (collapseInterval s I (not_duplicate_of_not_contains s I h)) := by
  simp only [ordinaryLift, dif_neg (not_duplicate_of_not_contains s I h), if_neg h]

theorem ordinaryLift_start (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left = A s) (hr : B s < I.right) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaPlus - t (collapse s I.right)) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_right_gt s I hr)) := by
  have hboth : intervalContainsBoth s I := ⟨le_of_eq hl, hr.le⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_right_gt s I hr), if_pos hboth, if_pos hl]

theorem ordinaryLift_end (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : I.right = B s) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaMinus - t (collapse s I.left)) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_left_lt s I hl)) := by
  have hboth : intervalContainsBoth s I := ⟨hl.le, le_of_eq hr.symm⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_left_lt s I hl), if_pos hboth,
    if_neg (ne_of_lt hl), if_pos hr]

theorem ordinaryLift_span (s : Fin n) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (I : BoundaryInterval (n + 1))
    (hl : I.left < A s) (hr : B s < I.right) :
    ordinaryLift s etaMinus etaPlus t b0 I =
      ((etaMinus + etaPlus) / 2) *
        b0 (collapseInterval s I (not_duplicate_of_left_lt s I hl)) := by
  have hboth : intervalContainsBoth s I := ⟨hl.le, hr.le⟩
  simp only [ordinaryLift, dif_neg (not_duplicate_of_left_lt s I hl), if_pos hboth,
    if_neg (ne_of_lt hl), if_neg (ne_of_gt hr)]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual three nonempty presentations: A only, B only, then both. -/
def spanningCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (i : Fin 3) : BoundaryCutSet I :=
  expandCuts s I hI C (spanningRows s I hI C hL hR hs i)

/-- Every old-section cut lies in the actual strict parent interval. -/
theorem spanning_old_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ old s k ∧ old s k ≤ I.right := by
  have hb := C.bounds k hk
  constructor
  · have hl := (old_strictMono s).monotone hb.1
    change old s (collapse s I.left) ≤ old s k at hl
    rwa [old_collapse_of_ne_B s I.left (ne_of_lt (lt_trans hL (A_lt_B s)))] at hl
  · have hr := (old_strictMono s).monotone hb.2
    change old s k ≤ old s (collapse s I.right) at hr
    rwa [old_collapse_of_ne_B s I.right (ne_of_gt hR)] at hr

/-- The tail section differs only at s, where B is strictly inside the parent. -/
theorem spanning_tail_cut_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (k : Fin n) (hk : k ∈ C.cuts) :
    I.left ≤ startingTailEmbedding s k ∧ startingTailEmbedding s k ≤ I.right := by
  by_cases he : k = s
  · subst k
    rw [startingTail_self]
    exact ⟨(lt_trans hL (A_lt_B s)).le, hR.le⟩
  · rw [startingTail_eq_old s k he]
    exact spanning_old_cut_bounds s I hI C hL hR k hk

theorem spanningCutSet_zero_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 0).cuts = C.cuts.image (old s) := by
  ext p
  have hm := mem_expandCuts s I hI C (spanningRows s I hI C hL hR hs 0) p
  change p ∈ (spanningCutSet s I hI C hL hR hs 0).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (spanningRows s I hI C hL hR hs 0).val at hm
  simp only [spanningRows, Matrix.cons_val_zero, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1, he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, hs, old_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, old_self])
    · left
      exact ⟨spanning_old_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_old] using hk, by simpa only [collapse_old] using hks⟩

theorem spanningCutSet_one_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 1).cuts = C.cuts.image (startingTailEmbedding s) := by
  ext p
  have hm := mem_expandCuts s I hI C (spanningRows s I hI C hL hR hs 1) p
  change p ∈ (spanningCutSet s I hI C hL hR hs 1).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (spanningRows s I hI C hL hR hs 1).val at hm
  have hrow : (spanningRows s I hI C hL hR hs 1).val = {B s} := rfl
  rw [hrow, Finset.mem_singleton] at hm
  rw [hm]
  constructor
  · rintro (h | rfl)
    · have he := (collapse_eq_iff_of_ne s (collapse s p) h.2.2 p).mp rfl
      exact Finset.mem_image.mpr ⟨collapse s p, h.2.1,
        (startingTail_eq_old s _ h.2.2).trans he.symm⟩
    · exact Finset.mem_image.mpr ⟨s, hs, startingTail_self s⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    by_cases hks : k = s
    · exact Or.inr (by rw [hks, startingTail_self])
    · left
      exact ⟨spanning_tail_cut_bounds s I hI C hL hR k hk,
        by simpa only [collapse_startingTail] using hk,
        by simpa only [collapse_startingTail] using hks⟩

/-- The both-cut row inserts exactly B into the A-only cut set. -/
theorem spanningCutSet_two_insert_B (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).cuts =
      insert (B s) (spanningCutSet s I hI C hL hR hs 0).cuts := by
  have hzero : (spanningRows s I hI C hL hR hs 0).val = {A s} := rfl
  have htwo : (spanningRows s I hI C hL hR hs 2).val = {A s, B s} := rfl
  ext p
  simp only [spanningCutSet, mem_expandCuts, hzero, htwo, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The same actual both-cut row inserts exactly A into the B-only cut set. -/
theorem spanningCutSet_two_insert_A (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCutSet s I hI C hL hR hs 2).cuts =
      insert (A s) (spanningCutSet s I hI C hL hR hs 1).cuts := by
  rw [spanningCutSet_two_insert_B, spanningCutSet_zero_cuts, spanningCutSet_one_cuts]
  exact starting_sections_cut_image s C.cuts hs

/-- Every actual A-only child is precisely one old-image core child. -/
def spanningChildrenZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {K : BoundaryInterval (n + 1) // (spanningCutSet s I hI C hL hR hs 0).Consecutive K} :=
  consecutiveOrderedImageEquiv (startingOldEmbedding s) C _
    (spanningCutSet_zero_cuts s I hI C hL hR hs)

/-- Every actual B-only child is precisely one tail-image core child. -/
def spanningChildrenOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {K : BoundaryInterval (n + 1) // (spanningCutSet s I hI C hL hR hs 1).Consecutive K} :=
  consecutiveOrderedImageEquiv (startingTailEmbedding s) C _
    (spanningCutSet_one_cuts s I hI C hL hR hs)

end
end SM.SoftDuplication


namespace SM

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

namespace BoundaryCutSet
variable {I : BoundaryInterval n}

/-- Every complete cut set is one raw source composition. -/
instance fintype : Fintype (BoundaryCutSet I) :=
  Fintype.ofEquiv (IntervalComposition I) (IntervalComposition.cutSetEquiv I)

/-- Reindex an interior cut by its actual boundary position. -/
def interiorIndexEquiv (S : BoundaryCutSet I) :
    Fin (S.toComposition.parts - 1) ≃ {x : Fin n // x ∈ S.interior.val} :=
  Equiv.ofBijective (fun k => ⟨S.toComposition.interiorPosition k, by
    simpa only [S.toComposition_cutSet] using S.toComposition.interiorPosition_mem k⟩)
    ⟨by
      intro k l he
      exact S.toComposition.interiorPosition_injective
        (congrArg (fun x : {x : Fin n // x ∈ S.interior.val} => x.val) he), by
      intro x
      have hx : x.val ∈ S.toComposition.cutSet.interior.val := by
        simpa only [S.toComposition_cutSet] using x.property
      obtain ⟨k, hk⟩ := (S.toComposition.mem_interior_iff_exists_index x.val).mp hx
      exact ⟨k, Subtype.ext hk⟩⟩

/-- Reindex all children by the actual consecutive pairs of cuts. -/
def partIndexEquiv (S : BoundaryCutSet I) :
    Fin S.toComposition.parts ≃ {J : BoundaryInterval n // S.Consecutive J} :=
  Equiv.ofBijective (fun k => ⟨S.toComposition.part k, by
    simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive k⟩)
    ⟨by
      intro k l he
      exact S.toComposition.part_injective (congrArg Subtype.val he), by
      intro J
      have hJ : S.toComposition.cutSet.Consecutive J.val := by
        simpa only [S.toComposition_cutSet] using J.property
      obtain ⟨k, hk⟩ := S.toComposition.exists_part_of_consecutive J.val hJ
      exact ⟨k, Subtype.ext hk⟩⟩

instance consecutiveFintype (S : BoundaryCutSet I) :
    Fintype {J : BoundaryInterval n // S.Consecutive J} :=
  Fintype.ofEquiv (Fin S.toComposition.parts) S.partIndexEquiv

/-- The near triple at this actual interior cut uses its two neighboring cuts. -/
def nearAtCut (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    IncreasingBoundaryTriple n :=
  S.toComposition.nearTriple (S.interiorIndexEquiv.symm x)

/-- The far triple uses the full interval endpoints and this actual cut. -/
def farAtCut (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    IncreasingBoundaryTriple n :=
  S.toComposition.farTriple (S.interiorIndexEquiv.symm x)

theorem nearAtCut_middle (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.nearAtCut x).middle = x.val := by
  change S.toComposition.interiorPosition (S.interiorIndexEquiv.symm x) = x.val
  exact congrArg Subtype.val (S.interiorIndexEquiv.apply_symm_apply x)

theorem farAtCut_middle (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.farAtCut x).middle = x.val := by
  change S.toComposition.interiorPosition (S.interiorIndexEquiv.symm x) = x.val
  exact congrArg Subtype.val (S.interiorIndexEquiv.apply_symm_apply x)

theorem farAtCut_lower (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.farAtCut x).lower = I.left := rfl

theorem farAtCut_upper (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : (S.farAtCut x).upper = I.right := rfl

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The complete summand, indexed by actual interior cuts and consecutive
child intervals. No nonunary restriction or nonzero factor is imposed. -/
def nearFarSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (S : BoundaryCutSet I) : R :=
  (∏ x : {x : Fin n // x ∈ S.interior.val},
    (D (S.nearAtCut x) - H (S.farAtCut x)) * ⅟ (2 : R)) *
    ∏ J : {J : BoundaryInterval n // S.Consecutive J}, X J.val

theorem nearFarSummand_toComposition (D H : TripleArray n R) (X : IntervalArray n R)
    (S : BoundaryCutSet I) :
    S.nearFarSummand D H X = S.toComposition.nearFarWeight D H *
      ∏ k : Fin S.toComposition.parts, X (S.toComposition.part k) := by
  have hg : S.toComposition.nearFarWeight D H =
      ∏ x : {x : Fin n // x ∈ S.interior.val},
        (D (S.nearAtCut x) - H (S.farAtCut x)) * ⅟ (2 : R) := by
    unfold IntervalComposition.nearFarWeight
    apply Fintype.prod_equiv S.interiorIndexEquiv
    intro k
    simp only [nearAtCut, farAtCut, Equiv.symm_apply_apply]
  have hp : (∏ k : Fin S.toComposition.parts, X (S.toComposition.part k)) =
      ∏ J : {J : BoundaryInterval n // S.Consecutive J}, X J.val :=
    Fintype.prod_equiv S.partIndexEquiv _ _ (fun _ => rfl)
  exact (congrArg₂ (fun a b : R => a * b) hg hp).symm

theorem nearFarSummand_cutSet (D H : TripleArray n R) (X : IntervalArray n R)
    (π : IntervalComposition I) :
    π.cutSet.nearFarSummand D H X = π.nearFarWeight D H *
      ∏ k : Fin π.parts, X (π.part k) := by
  rw [nearFarSummand_toComposition, IntervalComposition.cutSet_toComposition]

end BoundaryCutSet

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Reindex the complete source transform by all complete cut sets.
Every composition, including the one-part term, occurs exactly once. -/
theorem nearFarTransform_eq_cutSet_sum (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    nearFarTransform D H X I = ∑ S : BoundaryCutSet I, S.nearFarSummand D H X := by
  apply Fintype.sum_equiv (IntervalComposition.cutSetEquiv I)
  intro π
  exact (BoundaryCutSet.nearFarSummand_cutSet D H X π).symm

end
end SM


namespace SM.BoundaryCutSet

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Two consecutive intervals with the same right endpoint have the same
left endpoint: either strict ordering would expose an intervening cut. -/
theorem consecutive_left_unique (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hr : J.right = K.right) :
    J.left = K.left := by
  rcases lt_trichotomy J.left K.left with h | h | h
  · exact False.elim (hJ.2.2 K.left hK.1 ⟨h, by rw [hr]; exact K.increasing⟩)
  · exact h
  · exact False.elim (hK.2.2 J.left hJ.1 ⟨h, by rw [← hr]; exact J.increasing⟩)

theorem consecutive_right_unique (S : BoundaryCutSet I) {J K : BoundaryInterval n}
    (hJ : S.Consecutive J) (hK : S.Consecutive K) (hl : J.left = K.left) :
    J.right = K.right := by
  rcases lt_trichotomy J.right K.right with h | h | h
  · exact False.elim (hK.2.2 J.right hJ.2.1 ⟨by rw [← hl]; exact J.increasing, h⟩)
  · exact h
  · exact False.elim (hJ.2.2 K.right hK.2.1 ⟨by rw [hl]; exact K.increasing, h⟩)

/-- The physical child interval ending at this interior cut. -/
def nearLeftInterval (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    BoundaryInterval n where
  left := (S.nearAtCut x).lower
  right := (S.nearAtCut x).middle
  increasing := (S.nearAtCut x).lower_middle

/-- The physical child interval beginning at this interior cut. -/
def nearRightInterval (S : BoundaryCutSet I) (x : {x : Fin n // x ∈ S.interior.val}) :
    BoundaryInterval n where
  left := (S.nearAtCut x).middle
  right := (S.nearAtCut x).upper
  increasing := (S.nearAtCut x).middle_upper

theorem nearLeftInterval_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : S.Consecutive (S.nearLeftInterval x) := by
  let k := S.interiorIndexEquiv.symm x
  let l : Fin S.toComposition.parts := ⟨k.val, by have := k.isLt; omega⟩
  have he : S.nearLeftInterval x = S.toComposition.part l := rfl
  rw [he]
  simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive l

theorem nearRightInterval_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) : S.Consecutive (S.nearRightInterval x) := by
  let k := S.interiorIndexEquiv.symm x
  let l : Fin S.toComposition.parts := ⟨k.val + 1, by have := k.isLt; omega⟩
  have he : S.nearRightInterval x = S.toComposition.part l := rfl
  rw [he]
  simpa only [S.toComposition_cutSet] using S.toComposition.part_consecutive l

/-- Any geometric proof that J is the preceding consecutive child identifies
the actual near gate's lower argument. No enumeration correspondence is assumed. -/
theorem nearAtCut_lower_eq_of_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) (J : BoundaryInterval n)
    (hJ : S.Consecutive J) (hr : J.right = x.val) :
    (S.nearAtCut x).lower = J.left := by
  apply S.consecutive_left_unique (S.nearLeftInterval_consecutive x) hJ
  exact (S.nearAtCut_middle x).trans hr.symm

theorem nearAtCut_upper_eq_of_consecutive (S : BoundaryCutSet I)
    (x : {x : Fin n // x ∈ S.interior.val}) (J : BoundaryInterval n)
    (hJ : S.Consecutive J) (hl : J.left = x.val) :
    (S.nearAtCut x).upper = J.right := by
  apply S.consecutive_right_unique (S.nearRightInterval_consecutive x) hJ
  exact (S.nearAtCut_middle x).trans hl.symm

end
end SM.BoundaryCutSet


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- A cut at s is strictly interior in a genuinely spanning collapsed interval. -/
theorem spanning_core_cut_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    s ∈ C.interior.val := by
  have hb := span_collapsed_bounds s I hL hR
  exact Finset.mem_erase.mpr ⟨ne_of_lt hb.2,
    Finset.mem_erase.mpr ⟨ne_of_gt hb.1, hs⟩⟩

/-- The actual distinguished interior cut; no neighbor data is a parameter. -/
def spanningCoreCut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    {k : Fin n // k ∈ C.interior.val} :=
  ⟨s, spanning_core_cut_interior s I hI C hL hR hs⟩

theorem spanningCoreCut_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningCoreCut s I hI C hL hR hs).val = s := rfl

/-- The adjacent children are the existing actual near-interval constructions. -/
def spanningLeftChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : BoundaryInterval n :=
  C.nearLeftInterval (spanningCoreCut s I hI C hL hR hs)

def spanningRightChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : BoundaryInterval n :=
  C.nearRightInterval (spanningCoreCut s I hI C hL hR hs)

def spanningLeftNeighbor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : Fin n :=
  (spanningLeftChild s I hI C hL hR hs).left

def spanningRightNeighbor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) : Fin n :=
  (spanningRightChild s I hI C hL hR hs).right

theorem spanning_left_child_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    C.Consecutive (spanningLeftChild s I hI C hL hR hs) :=
  C.nearLeftInterval_consecutive (spanningCoreCut s I hI C hL hR hs)

theorem spanning_right_child_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    C.Consecutive (spanningRightChild s I hI C hL hR hs) :=
  C.nearRightInterval_consecutive (spanningCoreCut s I hI C hL hR hs)

theorem spanning_left_child_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningLeftChild s I hI C hL hR hs).left = spanningLeftNeighbor s I hI C hL hR hs ∧
    (spanningLeftChild s I hI C hL hR hs).right = s :=
  ⟨rfl, C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs)⟩

theorem spanning_right_child_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (spanningRightChild s I hI C hL hR hs).left = s ∧
    (spanningRightChild s I hI C hL hR hs).right = spanningRightNeighbor s I hI C hL hR hs :=
  ⟨C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs), rfl⟩

/-- Both actual neighboring cuts are in the full core cut set. -/
theorem spanning_neighbors_mem (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    spanningLeftNeighbor s I hI C hL hR hs ∈ C.cuts ∧
      spanningRightNeighbor s I hI C hL hR hs ∈ C.cuts :=
  ⟨(spanning_left_child_consecutive s I hI C hL hR hs).1,
    (spanning_right_child_consecutive s I hI C hL hR hs).2.1⟩

/-- In particular neither neighbor is s; the later t-values are read away from s. -/
theorem spanning_neighbors_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    (collapseInterval s I hI).left ≤ spanningLeftNeighbor s I hI C hL hR hs ∧
    spanningLeftNeighbor s I hI C hL hR hs < s ∧
    s < spanningRightNeighbor s I hI C hL hR hs ∧
    spanningRightNeighbor s I hI C hL hR hs ≤ (collapseInterval s I hI).right := by
  let x := spanningCoreCut s I hI C hL hR hs
  have hm : (C.nearAtCut x).middle = s := C.nearAtCut_middle x
  have hc := spanning_neighbors_mem s I hI C hL hR hs
  exact ⟨(C.bounds _ hc.1).1,
    lt_of_lt_of_eq (C.nearAtCut x).lower_middle hm,
    lt_of_eq_of_lt hm.symm (C.nearAtCut x).middle_upper,
    (C.bounds _ hc.2).2⟩

/-- Every actual consecutive child ending at s is the specified left child. -/
theorem spanning_left_child_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hr : K.right = s) :
    K = spanningLeftChild s I hI C hL hR hs :=
  C.consecutive_eq_of_right hK (spanning_left_child_consecutive s I hI C hL hR hs)
    (hr.trans (spanning_left_child_endpoints s I hI C hL hR hs).2.symm)

/-- Every actual consecutive child starting at s is the specified right child. -/
theorem spanning_right_child_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hl : K.left = s) :
    K = spanningRightChild s I hI C hL hR hs :=
  C.consecutive_eq_of_left hK (spanning_right_child_consecutive s I hI C hL hR hs)
    (hl.trans (spanning_right_child_endpoints s I hI C hL hR hs).1.symm)

theorem spanning_children_ne (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    spanningLeftChild s I hI C hL hR hs ≠ spanningRightChild s I hI C hL hR hs := by
  intro he
  have h := congrArg BoundaryInterval.right he
  let x := spanningCoreCut s I hI C hL hR hs
  change (C.nearAtCut x).middle = (C.nearAtCut x).upper at h
  exact (ne_of_lt (C.nearAtCut x).middle_upper) h

/-- The core cut has genuine adjacent parts; this is derived, not a nonunary premise. -/
theorem spanning_core_parts_ge_two (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    2 ≤ C.toComposition.parts := by
  have hb := (C.interiorIndexEquiv.symm (spanningCoreCut s I hI C hL hR hs)).isLt
  omega

theorem spanning_core_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    let T := C.nearAtCut (spanningCoreCut s I hI C hL hR hs)
    T.lower = spanningLeftNeighbor s I hI C hL hR hs ∧ T.middle = s ∧
      T.upper = spanningRightNeighbor s I hI C hL hR hs :=
  ⟨rfl, C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs), rfl⟩

theorem spanning_core_far_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) :
    let T := C.farAtCut (spanningCoreCut s I hI C hL hR hs)
    T.lower = (collapseInterval s I hI).left ∧ T.middle = s ∧
      T.upper = (collapseInterval s I hI).right :=
  ⟨rfl, C.farAtCut_middle (spanningCoreCut s I hI C hL hR hs), rfl⟩

/-- The source a is exactly t at the derived left neighboring cut, with no
hypothesis at the distinguished occurrence or on either rational value. -/
theorem spanning_coreNear_value (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts) (t : Fin n → ℚ) :
    coreNear s t (C.nearAtCut (spanningCoreCut s I hI C hL hR hs)) =
      t (spanningLeftNeighbor s I hI C hL hR hs) :=
  coreNear_at_middle s t _ (C.nearAtCut_middle (spanningCoreCut s I hI C hL hR hs))

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Interior membership removes precisely the two fixed endpoint cuts. -/
theorem starting_mem_interior_iff {m : ℕ} [NeZero m] {J : BoundaryInterval m}
    (C : BoundaryCutSet J) (k : Fin m) :
    k ∈ C.interior.val ↔ k ∈ C.cuts ∧ J.left < k ∧ k < J.right := by
  constructor
  · intro hk
    refine ⟨?_, C.interior.property k hk⟩
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
  · rintro ⟨hk, hl, hr⟩
    exact Finset.mem_erase.mpr ⟨ne_of_lt hr,
      Finset.mem_erase.mpr ⟨ne_of_gt hl, hk⟩⟩

theorem starting_old_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left = A s) (hR : B s < I.right) :
    old s (collapseInterval s I hI).left = I.left ∧
      old s (collapseInterval s I hI).right = I.right := by
  constructor
  · rw [starting_core_left s I hI hL, old_self, hL]
  · exact old_collapse_of_ne_B s I.right (ne_of_gt hR)

/-- The distinguished endpoint is never a core interior gate. -/
theorem starting_interior_gt (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (x : {k : Fin n // k ∈ C.interior.val}) : s < x.val := by
  have hx := (C.interior.property x.val x.property).1
  simpa only [starting_core_left s I hI hL] using hx

/-- Row zero retains exactly the old images of the core interior cuts. -/
theorem starting_zero_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 0).interior.val = C.interior.val.image (old s) := by
  have he := starting_old_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [startingCutSet_zero_cuts] at hpc
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
    · rw [startingCutSet_zero_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm (old_strictMono s hkl)
    · exact lt_of_lt_of_eq (old_strictMono s hkr) he.2

/-- Row one adds precisely the new interior position B. -/
theorem starting_one_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (startingCutSet s I hI C hL hR 1).interior.val =
      insert (B s) (C.interior.val.image (old s)) := by
  rw [← starting_zero_interior s I hI C hL hR]
  ext p
  simp only [starting_mem_interior_iff, startingCutSet_one_insert_B, Finset.mem_insert]
  constructor
  · rintro ⟨hp, hl, hr⟩
    exact hp.elim Or.inl (fun h => Or.inr ⟨h, hl, hr⟩)
  · rintro (rfl | ⟨hp, hl, hr⟩)
    · exact ⟨Or.inl rfl, by rw [hL]; exact A_lt_B s, hR⟩
    · exact ⟨Or.inr hp, hl, hr⟩

def startingInteriorZeroMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 0).interior.val} :=
  ⟨old s x.val, by
    rw [starting_zero_interior]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- The actual old-position map, with every core interior cut represented once. -/
def startingInteriorZeroEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 0).interior.val} :=
  Equiv.ofBijective (startingInteriorZeroMap s I hI C hL hR) ⟨by
    intro x y he
    apply Subtype.ext
    exact old_injective s (congrArg Subtype.val he), by
    intro p
    have hp : p.val ∈ C.interior.val.image (old s) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (starting_zero_interior s I hI C hL hR)) p.property
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp] theorem startingInteriorZeroEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((startingInteriorZeroEquiv s I hI C hL hR) x).val = old s x.val := rfl

def startingInteriorOneMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    Unit ⊕ {k : Fin n // k ∈ C.interior.val} →
      {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 1).interior.val}
  | Sum.inl _ => ⟨B s, by rw [starting_one_interior]; exact Finset.mem_insert_self _ _⟩
  | Sum.inr x => ⟨old s x.val, by
      rw [starting_one_interior]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)⟩

/-- The new B gate and all inherited gates form a disjoint, exhaustive domain. -/
def startingInteriorOneEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    (Unit ⊕ {k : Fin n // k ∈ C.interior.val}) ≃
      {p : Fin (n + 1) // p ∈ (startingCutSet s I hI C hL hR 1).interior.val} :=
  Equiv.ofBijective (startingInteriorOneMap s I hI C hL hR) ⟨by
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
        (starting_one_interior s I hI C hL hR)) p.property
    rcases Finset.mem_insert.mp hp with he | hp
    · exact ⟨Sum.inl (), Subtype.ext he.symm⟩
    · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
      exact ⟨Sum.inr ⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp] theorem startingInteriorOneEquiv_inl_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (u : Unit) :
    ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inl u)).val = B s := rfl

@[simp] theorem startingInteriorOneEquiv_inr_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)).val = old s x.val := rfl

/-- Both actual near neighbors in row zero are old images of core neighbors. -/
theorem starting_zero_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 0).nearAtCut
        ((startingInteriorZeroEquiv s I hI C hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := startingCutSet s I hI C hL hR 0
  let y := (startingInteriorZeroEquiv s I hI C hL hR) x
  have hl := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (startingCutSet_zero_cuts s I hI C hL hR) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (startingCutSet_zero_cuts s I hI C hL hR) (C.nearRightInterval x)).mpr
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

theorem starting_zero_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 0).farAtCut
        ((startingInteriorZeroEquiv s I hI C hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := starting_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((startingCutSet s I hI C hL hR 0).farAtCut
        ((startingInteriorZeroEquiv s I hI C hL hR) x)).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- Row one's inherited near triples use the tail section, including its B endpoint. -/
theorem starting_one_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 1).nearAtCut
        ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingTailEmbedding s) (C.nearAtCut x) := by
  let S := startingCutSet s I hI C hL hR 1
  let y := (startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)
  have hx : startingTailEmbedding s x.val = old s x.val :=
    startingTail_eq_old s x.val (ne_of_gt (starting_interior_gt s I hI C hL x))
  have hl := starting_one_mapped_consecutive s I hI C hL hR
    (C.nearLeftInterval x) (C.nearLeftInterval_consecutive x)
  have hr := starting_one_mapped_consecutive s I hI C hL hR
    (C.nearRightInterval x) (C.nearRightInterval_consecutive x)
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact S.nearAtCut_lower_eq_of_consecutive y _ hl (by
      change startingTailEmbedding s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle, hx])
  · change (S.nearAtCut y).middle = startingTailEmbedding s (C.nearAtCut x).middle
    rw [S.nearAtCut_middle, C.nearAtCut_middle, hx]
    rfl
  · exact S.nearAtCut_upper_eq_of_consecutive y _ hr (by
      change startingTailEmbedding s (C.nearAtCut x).middle = old s x.val
      rw [C.nearAtCut_middle, hx])

/-- Far triples retain the full parent left endpoint A, even in row one. -/
theorem starting_one_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (startingCutSet s I hI C hL hR 1).farAtCut
        ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x)) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := starting_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((startingCutSet s I hI C hL hR 1).farAtCut
        ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inr x))).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm

/-- The new B gate sees the actual singleton on its left and first tail child on its right. -/
theorem starting_new_near_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    let T := (startingCutSet s I hI C hL hR 1).nearAtCut
      ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inl ()))
    T.lower = A s ∧ T.middle = B s ∧
      T.upper = old s (startingFirstChild s I hI C).right := by
  let S := startingCutSet s I hI C hL hR 1
  let y := (startingInteriorOneEquiv s I hI C hL hR) (Sum.inl ())
  have hl := starting_one_duplicate_consecutive s I hI C hL hR
  have hr := starting_one_mapped_consecutive s I hI C hL hR
    (startingFirstChild s I hI C) (startingFirstChild_consecutive s I hI C)
  have he := starting_first_one_endpoints s I hI C hL
  refine ⟨?_, ?_, ?_⟩
  · exact S.nearAtCut_lower_eq_of_consecutive y (duplicateInterval s) hl rfl
  · exact S.nearAtCut_middle y
  · exact (S.nearAtCut_upper_eq_of_consecutive y
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) (startingFirstChild s I hI C))
      hr he.1).trans he.2

theorem starting_new_far_positions (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) :
    let T := (startingCutSet s I hI C hL hR 1).farAtCut
      ((startingInteriorOneEquiv s I hI C hL hR) (Sum.inl ()))
    T.lower = A s ∧ T.middle = B s ∧ T.upper = I.right := by
  refine ⟨hL, ?_, rfl⟩
  exact (startingCutSet s I hI C hL hR 1).farAtCut_middle _

end
end SM.SoftDuplication


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


namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The concrete old-section ordered triple is the previously defined old triple. -/
theorem startingOld_triple_eq (s : Fin n) (T : IncreasingBoundaryTriple n) :
    OrderedBoundaryTransport.triple (startingOldEmbedding s) T = oldTriple s T := by
  apply triple_ext <;> rfl

/-- The actual alternate section omits A, including at either endpoint. -/
theorem startingTail_ne_A (s k : Fin n) : startingTailEmbedding s k ≠ A s :=
  Fin.succAbove_ne (A s) k

/-- A tail image cannot contain both occurrences because it contains no A. -/
theorem startingTail_triple_plain (s : Fin n) (T : IncreasingBoundaryTriple n) :
    ¬ tripleContainsBoth s (OrderedBoundaryTransport.triple (startingTailEmbedding s) T) := by
  intro h
  rcases h.1 with h | h | h
  · exact startingTail_ne_A s T.lower h
  · exact startingTail_ne_A s T.middle h
  · exact startingTail_ne_A s T.upper h

/-- Collapse recovers every actual tail triple, with no caller-supplied section. -/
theorem collapse_startingTail_triple (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hplain : ¬ tripleContainsBoth s
      (OrderedBoundaryTransport.triple (startingTailEmbedding s) T)) :
    collapseTriple s (OrderedBoundaryTransport.triple (startingTailEmbedding s) T) hplain = T := by
  apply triple_ext
  · exact collapse_startingTail s T.lower
  · exact collapse_startingTail s T.middle
  · exact collapse_startingTail s T.upper

/-- Every actual old-image gate has the exact core array value. -/
theorem tripleLift_startingOld {R : Type*} (s : Fin n) (H0 : TripleArray n R)
    (t : Fin n → R) (T : IncreasingBoundaryTriple n) :
    tripleLift s H0 t (OrderedBoundaryTransport.triple (startingOldEmbedding s) T) = H0 T := by
  rw [startingOld_triple_eq, tripleLift_oldTriple]

/-- Every actual tail-image gate has the exact core array value. -/
theorem tripleLift_startingTail {R : Type*} (s : Fin n) (H0 : TripleArray n R)
    (t : Fin n → R) (T : IncreasingBoundaryTriple n) :
    tripleLift s H0 t (OrderedBoundaryTransport.triple (startingTailEmbedding s) T) = H0 T := by
  rw [tripleLift_plain s H0 t _ (startingTail_triple_plain s T),
    collapse_startingTail_triple]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complete product over actual interior cuts, with rational gate entries. -/
def cutGateProduct {m : ℕ} [NeZero m] {I : BoundaryInterval m}
    (C : BoundaryCutSet I) (D H : TripleArray m ℚ) : ℚ :=
  ∏ x : {x : Fin m // x ∈ C.interior.val},
    (D (C.nearAtCut x) - H (C.farAtCut x)) / 2

/-- Separate the complete actual gate and child products without cancelling either. -/
theorem nearFarSummand_eq_cutGateProduct {m : ℕ} [NeZero m] {I : BoundaryInterval m}
    (C : BoundaryCutSet I) (D H : TripleArray m ℚ) (b : IntervalArray m ℚ) :
    C.nearFarSummand D H b = cutGateProduct C D H *
      ∏ K : {K : BoundaryInterval m // C.Consecutive K}, b K.val := by
  simp only [BoundaryCutSet.nearFarSummand, cutGateProduct, div_eq_mul_inv, invOf_eq_inv]

variable {n : ℕ} [NeZero n]

/-- Row zero's actual near and far gates evaluate to their core entries. -/
theorem starting_zero_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((startingCutSet s I hI C hL hR 0).nearAtCut
      (startingInteriorZeroEquiv s I hI C hL hR x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((startingCutSet s I hI C hL hR 0).farAtCut
      (startingInteriorZeroEquiv s I hI C hL hR x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [starting_zero_nearTriple, tripleLift_startingOld]
  · rw [starting_zero_farTriple, tripleLift_startingOld]

/-- Row one's inherited near triple is a tail image, while its far triple is
an old image. Both are evaluated at their actual core triples. -/
theorem starting_one_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((startingCutSet s I hI C hL hR 1).nearAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inr x))) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((startingCutSet s I hI C hL hR 1).farAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inr x))) = H0 (C.farAtCut x) := by
  constructor
  · rw [starting_one_nearTriple, tripleLift_startingTail]
  · rw [starting_one_farTriple, tripleLift_startingOld]

/-- The additional B gate has exactly the first-child near argument and full
interval far argument, including a unary core composition. -/
theorem starting_new_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    tripleLift s D0 tD ((startingCutSet s I hI C hL hR 1).nearAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inl ()))) =
        tD (startingFirstChild s I hI C).right ∧
    tripleLift s H0 tH ((startingCutSet s I hI C hL hR 1).farAtCut
      (startingInteriorOneEquiv s I hI C hL hR (Sum.inl ()))) =
        tH (collapseInterval s I hI).right := by
  have hn := starting_new_near_positions s I hI C hL hR
  have hf := starting_new_far_positions s I hI C hL hR
  constructor
  · rw [tripleLift_lower s D0 tD _ ⟨hn.1, hn.2.1⟩, hn.2.2, collapse_old]
  · rw [tripleLift_lower s H0 tH _ ⟨hf.1, hf.2.1⟩, hf.2.2]
    rfl

/-- The complete row-zero gate product is the actual core gate product. -/
theorem starting_zero_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (startingCutSet s I hI C hL hR 0)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (startingInteriorZeroEquiv s I hI C hL hR)
  intro x
  have h := starting_zero_gate_values s I hI C hL hR D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete row-one gate product includes exactly its additional B gate.
The core interior product may be empty and any gate may be zero. -/
theorem starting_one_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (startingCutSet s I hI C hL hR 1)
      (tripleLift s D0 tD) (tripleLift s H0 tH) =
      ((tD (startingFirstChild s I hI C).right - tH (collapseInterval s I hI).right) / 2) *
        cutGateProduct C D0 H0 := by
  calc
    _ = ∏ x : Unit ⊕ {x : Fin n // x ∈ C.interior.val},
        (tripleLift s D0 tD ((startingCutSet s I hI C hL hR 1).nearAtCut
            (startingInteriorOneEquiv s I hI C hL hR x)) -
          tripleLift s H0 tH ((startingCutSet s I hI C hL hR 1).farAtCut
            (startingInteriorOneEquiv s I hI C hL hR x))) / 2 :=
      (Fintype.prod_equiv (startingInteriorOneEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_unique]
      have h := starting_new_gate_values s I hI C hL hR D0 H0 tD tH
      rw [h.1, h.2]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have h := starting_one_gate_values s I hI C hL hR D0 H0 tD tH x
      rw [h.1, h.2]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Actual zero row near/far values are the complete core entries. -/
theorem spanning_zero_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ)
    (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((spanningCutSet s I hI C hL hR hs 0).nearAtCut
      (spanningInteriorZeroEquiv s I hI C hL hR hs x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((spanningCutSet s I hI C hL hR hs 0).farAtCut
      (spanningInteriorZeroEquiv s I hI C hL hR hs x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [spanning_zero_nearTriple, tripleLift_startingOld]
  · rw [spanning_zero_farTriple, tripleLift_startingOld]

/-- Actual one row near/far values are the complete core entries. -/
theorem spanning_one_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ)
    (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((spanningCutSet s I hI C hL hR hs 1).nearAtCut
      (spanningInteriorOneEquiv s I hI C hL hR hs x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((spanningCutSet s I hI C hL hR hs 1).farAtCut
      (spanningInteriorOneEquiv s I hI C hL hR hs x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [spanning_one_nearTriple, tripleLift_startingTail]
  · rw [spanning_one_farTriple, tripleLift_startingTail]

/-- All inherited both-row gates have the actual core values, including A at core s. -/
theorem spanning_two_inherited_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t u : Fin n → ℚ)
    (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s (coreNear s t) t ((spanningCutSet s I hI C hL hR hs 2).nearAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inr x))) = coreNear s t (C.nearAtCut x) ∧
    tripleLift s H0 u ((spanningCutSet s I hI C hL hR hs 2).farAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inr x))) = H0 (C.farAtCut x) := by
  constructor
  · by_cases hx : x.val = s
    · have he : x = spanningCoreCut s I hI C hL hR hs := Subtype.ext hx
      subst x
      have hp := spanning_two_A_near_positions s I hI C hL hR hs
      rw [tripleLift_upper s (coreNear s t) t _ ⟨hp.2.1, hp.2.2⟩,
        hp.1, collapse_old, spanning_coreNear_value]
    · rcases lt_or_gt_of_ne hx with hl | hr
      · rw [spanning_two_nearTriple_of_lt s I hI C hL hR hs x hl, tripleLift_startingOld]
      · rw [spanning_two_nearTriple_of_gt s I hI C hL hR hs x hr, tripleLift_startingTail]
  · rw [spanning_two_farTriple, tripleLift_startingOld]

/-- The additional B gate has near t(R) and the same actual core far value at s. -/
theorem spanning_two_new_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (t u : Fin n → ℚ) :
    tripleLift s D0 t ((spanningCutSet s I hI C hL hR hs 2).nearAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inl ()))) =
        t (spanningRightNeighbor s I hI C hL hR hs) ∧
    tripleLift s H0 u ((spanningCutSet s I hI C hL hR hs 2).farAtCut
      (spanningInteriorTwoEquiv s I hI C hL hR hs (Sum.inl ()))) =
        H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs)) := by
  have hp := spanning_two_B_near_positions s I hI C hL hR hs
  constructor
  · rw [tripleLift_lower s D0 t _ ⟨hp.1, hp.2.1⟩, hp.2.2, collapse_startingTail]
  · rw [spanning_two_B_farTriple, tripleLift_startingTail]

/-- The complete zero row gate product is exactly the core product, with no division. -/
theorem spanning_zero_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ) :
    cutGateProduct (spanningCutSet s I hI C hL hR hs 0)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (spanningInteriorZeroEquiv s I hI C hL hR hs)
  intro x
  have h := spanning_zero_gate_values s I hI C hL hR hs D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete one row gate product is exactly the core product, with no division. -/
theorem spanning_one_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ) :
    cutGateProduct (spanningCutSet s I hI C hL hR hs 1)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (spanningInteriorOneEquiv s I hI C hL hR hs)
  intro x
  have h := spanning_one_gate_values s I hI C hL hR hs D0 H0 tD tH x
  rw [h.1, h.2]

/-- The complete both-row gate product adds just the B gate to every core gate. -/
theorem spanning_two_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t u : Fin n → ℚ) :
    cutGateProduct (spanningCutSet s I hI C hL hR hs 2)
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u) =
      ((t (spanningRightNeighbor s I hI C hL hR hs) -
        H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
        cutGateProduct C (coreNear s t) H0 := by
  calc
    _ = ∏ x : Unit ⊕ {x : Fin n // x ∈ C.interior.val},
        (tripleLift s (coreNear s t) t ((spanningCutSet s I hI C hL hR hs 2).nearAtCut
            (spanningInteriorTwoEquiv s I hI C hL hR hs x)) -
          tripleLift s H0 u ((spanningCutSet s I hI C hL hR hs 2).farAtCut
            (spanningInteriorTwoEquiv s I hI C hL hR hs x))) / 2 :=
      (Fintype.prod_equiv (spanningInteriorTwoEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_unique]
      have h := spanning_two_new_gate_values s I hI C hL hR hs (coreNear s t) H0 t u
      rw [h.1, h.2]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      have h := spanning_two_inherited_gate_values s I hI C hL hR hs H0 t u x
      rw [h.1, h.2]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- An increasing section of the actual collapse cannot map a genuine core
interval to the duplicate singleton. -/
theorem sectionInterval_not_duplicate (s : Fin n) (e : Fin n ↪o Fin (n + 1))
    (hsec : ∀ k, collapse s (e k) = k) (K : BoundaryInterval n) :
    OrderedBoundaryTransport.interval e K ≠ duplicateInterval s := by
  intro he
  have hc := (collapse_endpoints_eq_iff s (OrderedBoundaryTransport.interval e K)).mpr he
  change collapse s (e K.left) = collapse s (e K.right) at hc
  rw [hsec, hsec] at hc
  exact (ne_of_lt K.increasing) hc

/-- The collapsed image interval is exactly the original core interval. -/
theorem collapse_sectionInterval (s : Fin n) (e : Fin n ↪o Fin (n + 1))
    (hsec : ∀ k, collapse s (e k) = k) (K : BoundaryInterval n)
    (hI : OrderedBoundaryTransport.interval e K ≠ duplicateInterval s) :
    collapseInterval s (OrderedBoundaryTransport.interval e K) hI = K := by
  apply BoundaryInterval.eq_of_endpoints
  · exact hsec K.left
  · exact hsec K.right

/-- The old-mapped first core child receives exactly the source starting factor. -/
theorem starting_zero_first_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)) =
      ((etaPlus - t (startingFirstChild s I hI C).right) / 2) *
        b0 (startingFirstChild s I hI C) := by
  have h := starting_first_zero_endpoints s I hI C hL
  rw [ordinaryLift_start s etaMinus etaPlus t b0 _ h.1 h.2.2]
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (startingFirstChild s I hI C)).right =
      (startingFirstChild s I hI C).right := collapse_old s _
  rw [hc, collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Every other old-mapped child is plain and contributes its exact core value. -/
theorem starting_zero_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ startingFirstChild s I hI C) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hs := starting_otherChild_left_gt s I hI C hL K hK hne
  have ha : A s < old s K.left := by
    rw [← old_self s]
    exact old_strictMono s hs
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) :=
    fun h => (not_le_of_gt ha) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Each tail-mapped core child starts at or after B, so it is plain.
The section identity is proved for this concrete map, not a caller premise. -/
theorem starting_one_core_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) = b0 K := by
  have hs : s ≤ K.left := by
    simpa only [starting_core_left s I hI hL] using (C.bounds K.left hK.1).1
  have hb : B s ≤ startingTailEmbedding s K.left := by
    rw [← startingTail_self s]
    exact (startingTailEmbedding s).monotone hs
  have ha : A s < startingTailEmbedding s K.left := lt_of_lt_of_le (A_lt_B s) hb
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) :=
    fun h => (not_le_of_gt ha) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s)]

/-- Row zero's complete child product has precisely one exceptional factor.
Finite-product factorization permits every core child value to be zero. -/
theorem starting_zero_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (startingCutSet s I hI C hL hR 0).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaPlus - t (startingFirstChild s I hI C).right) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨startingFirstChild s I hI C, startingFirstChild_consecutive s I hI C⟩
  let m : ℚ := (etaPlus - t (startingFirstChild s I hI C).right) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val) :=
      (Fintype.prod_equiv (startingChildrenZeroEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact starting_zero_first_child_factor s I hI C hL etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact starting_zero_other_child_factor s I hI C hL etaMinus etaPlus t b0 K.val K.property
          (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- Row one's complete child product is the core product: the additional
actual [A,B] child has value1, and every tail child is transported exactly. -/
theorem starting_one_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left = A s) (hR : B s < I.right) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (startingCutSet s I hI C hL hR 1).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  calc
    _ = ∏ x : Unit ⊕ {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          ((startingChildrenOneEquiv s I hI C hL hR) x).val :=
      (Fintype.prod_equiv (startingChildrenOneEquiv s I hI C hL hR) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      change (∏ _u : Unit, ordinaryLift s etaMinus etaPlus t b0 (duplicateInterval s)) *
        (∏ K : {K : BoundaryInterval n // C.Consecutive K},
          ordinaryLift s etaMinus etaPlus t b0
            (OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val)) = _
      simp only [ordinaryLift_duplicate, Finset.prod_const_one, one_mul]
      apply Finset.prod_congr rfl
      intro K hK
      exact starting_one_core_child_factor s I hI C hL etaMinus etaPlus t b0 K.val K.property

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- In the A-only row, the actual right adjacent child receives the starting factor. -/
theorem spanning_zero_right_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s)
        (spanningRightChild s I hI C hL hR hs)) =
      ((etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2) *
        b0 (spanningRightChild s I hI C hL hR hs) := by
  let K := spanningRightChild s I hI C hL hR hs
  have he := spanning_right_child_endpoints s I hI C hL hR hs
  have hb := spanning_neighbors_bounds s I hI C hL hR hs
  have hl : old s K.left = A s := by rw [he.1, old_self]
  have hr : B s < old s K.right := by
    have hk : s.val < K.right.val := hb.2.2.1
    change s.val + 1 < (old s K.right).val
    rw [old_val, if_neg (by omega)]
    omega
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K).right = K.right :=
    collapse_old s K.right
  rw [ordinaryLift_start s etaMinus etaPlus t b0 _ hl hr,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s), hc]
  simp only [K, spanningRightNeighbor]

/-- Every other old-image child is plain, including the actual left adjacent child. -/
theorem spanning_zero_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningRightChild s I hI C hL hR hs) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
    by_cases hl : s < K.left
    · have ha : A s < old s K.left := by
        rw [← old_self s]
        exact old_strictMono s hl
      exact fun h => (not_le_of_gt ha) h.1
    · have hls : K.left < s := lt_of_le_of_ne (le_of_not_gt hl) (fun he =>
        hne (spanning_right_child_unique s I hI C hL hR hs K hK he))
      have hrs : K.right ≤ s := le_of_not_gt (fun hr => hK.2.2 s hs ⟨hls, hr⟩)
      have ha : old s K.right ≤ A s := by
        rw [← old_self s]
        exact (old_strictMono s).monotone hrs
      exact fun h => (not_le_of_gt (lt_of_le_of_lt ha (A_lt_B s))) h.2
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- In the B-only row, the actual left adjacent child receives the ending factor. -/
theorem spanning_one_left_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s)
        (spanningLeftChild s I hI C hL hR hs)) =
      ((etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2) *
        b0 (spanningLeftChild s I hI C hL hR hs) := by
  let K := spanningLeftChild s I hI C hL hR hs
  have he := spanning_left_child_endpoints s I hI C hL hR hs
  have hb := spanning_neighbors_bounds s I hI C hL hR hs
  have hl : startingTailEmbedding s K.left < A s := by
    rw [startingTail_eq_old s K.left (ne_of_lt hb.2.1), ← old_self s]
    exact old_strictMono s hb.2.1
  have hr : startingTailEmbedding s K.right = B s := by rw [he.2, startingTail_self]
  have hc : collapse s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K).left = K.left :=
    collapse_startingTail s K.left
  rw [ordinaryLift_end s etaMinus etaPlus t b0 _ hl hr,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s), hc]
  simp only [K, spanningLeftNeighbor]

/-- Every other tail-image child is plain, including the actual right adjacent child. -/
theorem spanning_one_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningLeftChild s I hI C hL hR hs) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) = b0 K := by
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingTailEmbedding s) K) := by
    by_cases hr : K.right < s
    · have hb : startingTailEmbedding s K.right < B s := by
        rw [← startingTail_self s]
        exact (startingTailEmbedding s).strictMono hr
      exact fun h => (not_le_of_gt hb) h.2
    · have hsr : s < K.right := lt_of_le_of_ne (le_of_not_gt hr) (fun he =>
        hne (spanning_left_child_unique s I hI C hL hR hs K hK he.symm))
      have hsl : s ≤ K.left := le_of_not_gt (fun hl => hK.2.2 s hs ⟨hl, hsr⟩)
      have hb : B s ≤ startingTailEmbedding s K.left := by
        rw [← startingTail_self s]
        exact (startingTailEmbedding s).monotone hsl
      exact fun h => (not_le_of_gt (lt_of_lt_of_le (A_lt_B s) hb)) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingTailEmbedding s) (collapse_startingTail s)]

/-- The complete A-only child product has just the actual right-child multiplier. -/
theorem spanning_zero_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (spanningCutSet s I hI C hL hR hs 0).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨spanningRightChild s I hI C hL hR hs, spanning_right_child_consecutive s I hI C hL hR hs⟩
  let m : ℚ := (etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val) :=
      (Fintype.prod_equiv (spanningChildrenZeroEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact spanning_zero_right_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact spanning_zero_other_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
          K.val K.property (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- The complete B-only child product has just the actual left-child multiplier. -/
theorem spanning_one_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (spanningCutSet s I hI C hL hR hs 1).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨spanningLeftChild s I hI C hL hR hs, spanning_left_child_consecutive s I hI C hL hR hs⟩
  let m : ℚ := (etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingTailEmbedding s) K.val) :=
      (Fintype.prod_equiv (spanningChildrenOneEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact spanning_one_left_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact spanning_one_other_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
          K.val K.property (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

end
end SM.SoftDuplication


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


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- Every actual inherited child in the both-cut row is plain and collapses to its core child. -/
theorem spanning_two_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∈ C.cuts) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (K : BoundaryInterval n) (hK : C.Consecutive K) :
    ordinaryLift s etaMinus etaPlus t b0 (spanningBothChild s K) = b0 K := by
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ (spanningBothChild_plain s I hI C hs K hK),
    spanningBothChild_collapse]

/-- The complete both-cut child product is the core product; its additional singleton has value1. -/
theorem spanning_two_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (spanningCutSet s I hI C hL hR hs 2).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  calc
    _ = ∏ x : Unit ⊕ {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          ((spanningChildrenBothEquiv s I hI C hL hR hs) x).val :=
      (Fintype.prod_equiv (spanningChildrenBothEquiv s I hI C hL hR hs) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [spanningChildrenBothEquiv_inl_val, spanningChildrenBothEquiv_inr_val,
        ordinaryLift_duplicate, Finset.prod_const_one, one_mul]
      apply Finset.prod_congr rfl
      intro K hK
      exact spanning_two_child_factor s I hI C hs etaMinus etaPlus t b0 K.val K.property

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual left neighbor is strictly below s, so its sign square is covered
by the off-s hypothesis. The far value is evaluated at the actual core far triple. -/
theorem spanning_core_far_square_of_signs (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2 := by
  have hb := spanning_neighbors_bounds s I hI C hL hR hs
  calc
    _ = 1 := hH _
    _ = _ := (ht _ (ne_of_lt hb.2.1)).symm

/-- Split the complete finite gate product at the actual core cut s. Multiplying
its gate (a-h)/2 by (a+h)/2 gives zero from h²=a², and the full exterior is retained. -/
theorem spanning_core_gate_cancellation (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hsq : (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2) :
    ((t (spanningLeftNeighbor s I hI C hL hR hs) +
      H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
      cutGateProduct C (coreNear s t) H0 = 0 := by
  let x0 := spanningCoreCut s I hI C hL hR hs
  let a := t (spanningLeftNeighbor s I hI C hL hR hs)
  let h := H0 (C.farAtCut x0)
  let f : {x : Fin n // x ∈ C.interior.val} → ℚ :=
    fun x => (coreNear s t (C.nearAtCut x) - H0 (C.farAtCut x)) / 2
  have hf0 : f x0 = (a - h) / 2 :=
    congrArg (fun v : ℚ => (v - h) / 2)
      (spanning_coreNear_value s I hI C hL hR hs t)
  have hp : cutGateProduct C (coreNear s t) H0 =
      f x0 * ∏ x ∈ Finset.univ.erase x0, f x :=
    (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x0)).symm
  have hsq' : h ^ 2 = a ^ 2 := hsq
  have hc : ((a + h) / 2) * f x0 = 0 := by
    rw [hf0]
    calc
      _ = (a ^ 2 - h ^ 2) / 4 := by ring
      _ = 0 := by rw [hsq']; ring
  change ((a + h) / 2) * cutGateProduct C (coreNear s t) H0 = 0
  rw [hp, ← mul_assoc, hc, zero_mul]

/-- The same local vanishing retains the complete product of all actual child
values. No gate, exterior or child factor is required to be nonzero. -/
theorem spanning_core_summand_cancellation (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hsq : (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2) :
    ((t (spanningLeftNeighbor s I hI C hL hR hs) +
      H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
      C.nearFarSummand (coreNear s t) H0 b0 = 0 := by
  rw [nearFarSummand_eq_cutGateProduct, ← mul_assoc,
    spanning_core_gate_cancellation s I hI C hL hR hs H0 t hsq, zero_mul]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The unique presentation when the core cut set omits the distinguished position. -/
def emptySpanningCutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : BoundaryCutSet I :=
  expandCuts s I hI C (emptyCutFiber s I hI C hs)

/-- The mandatory endpoints also avoid the missing core cut, so this identity
needs no extra exterior bounds on I. -/
theorem emptySpanningCutSet_cuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) : (emptySpanningCutSet s I hI C hs).cuts = C.cuts.image (old s) := by
  have hcl : collapse s I.left ≠ s := by
    intro he
    exact hs ((congrArg (fun k : Fin n => k ∈ C.cuts) he).mp C.left_mem)
  have hcr : collapse s I.right ≠ s := by
    intro he
    exact hs ((congrArg (fun k : Fin n => k ∈ C.cuts) he).mp C.right_mem)
  have hlB : I.left ≠ B s := by
    intro he
    exact hcl (by rw [he, collapse_B])
  have hrB : I.right ≠ B s := by
    intro he
    exact hcr (by rw [he, collapse_B])
  have bounds (k : Fin n) (hk : k ∈ C.cuts) :
      I.left ≤ old s k ∧ old s k ≤ I.right := by
    have hb := C.bounds k hk
    constructor
    · have hl := (old_strictMono s).monotone hb.1
      change old s (collapse s I.left) ≤ old s k at hl
      rwa [old_collapse_of_ne_B s I.left hlB] at hl
    · have hr := (old_strictMono s).monotone hb.2
      change old s k ≤ old s (collapse s I.right) at hr
      rwa [old_collapse_of_ne_B s I.right hrB] at hr
  ext p
  have hm := mem_expandCuts s I hI C (emptyCutFiber s I hI C hs) p
  change p ∈ (emptySpanningCutSet s I hI C hs).cuts ↔
    ((I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts ∧ collapse s p ≠ s) ∨
      p ∈ (emptyCutFiber s I hI C hs).val at hm
  simp only [emptyCutFiber, Finset.notMem_empty, or_false] at hm
  rw [hm]
  constructor
  · intro hp
    have he := (collapse_eq_iff_of_ne s (collapse s p) hp.2.2 p).mp rfl
    exact Finset.mem_image.mpr ⟨collapse s p, hp.2.1, he.symm⟩
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hks : k ≠ s := by
      intro he
      exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hk)
    exact ⟨bounds k hk, by simpa only [collapse_old] using hk,
      by simpa only [collapse_old] using hks⟩

theorem emptySpanningCutSet_old_mem (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (k : Fin n) :
    old s k ∈ (emptySpanningCutSet s I hI C hs).cuts ↔ k ∈ C.cuts := by
  rw [emptySpanningCutSet_cuts]
  exact cut_mem_ordered_image (startingOldEmbedding s) C k

/-- Every actual expanded child is one old-mapped core child, including unary C. -/
def emptySpanningChildrenEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) :
    {K : BoundaryInterval n // C.Consecutive K} ≃
      {J : BoundaryInterval (n + 1) // (emptySpanningCutSet s I hI C hs).Consecutive J} :=
  consecutiveOrderedImageEquiv (startingOldEmbedding s) C (emptySpanningCutSet s I hI C hs)
    (emptySpanningCutSet_cuts s I hI C hs)

@[simp]
theorem emptySpanningChildrenEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (K : {K : BoundaryInterval n // C.Consecutive K}) :
    ((emptySpanningChildrenEquiv s I hI C hs) K).val =
      OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val := rfl

/-- The canonical half-open part containing s is strictly spanning because s is not a cut. -/
theorem exists_spanning_part (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    ∃ k : Fin C.toComposition.parts,
      (C.toComposition.part k).left < s ∧ s < (C.toComposition.part k).right := by
  have hb : (collapseInterval s I hI).left < s ∧ s < (collapseInterval s I hI).right :=
    span_collapsed_bounds s I hL hR
  obtain ⟨k, hk⟩ := C.toComposition.exists_halfOpen_part s hb.1.le hb.2
  have hc : C.Consecutive (C.toComposition.part k) := by
    simpa only [BoundaryCutSet.toComposition_cutSet] using C.toComposition.part_consecutive k
  have hne : (C.toComposition.part k).left ≠ s := by
    intro he
    exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hc.1)
  exact ⟨k, lt_of_le_of_ne hk.1 hne, hk.2⟩

/-- This is an actual part of the complete core composition, not an assumed containing interval. -/
def spanningChild (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) : BoundaryInterval n :=
  C.toComposition.part (Classical.choose (exists_spanning_part s I hI C hL hR hs))

theorem spanningChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    C.Consecutive (spanningChild s I hI C hL hR hs) := by
  simpa only [spanningChild, BoundaryCutSet.toComposition_cutSet] using
    C.toComposition.part_consecutive (Classical.choose (exists_spanning_part s I hI C hL hR hs))

theorem spanningChild_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    (spanningChild s I hI C hL hR hs).left < s ∧
      s < (spanningChild s I hI C hL hR hs).right := by
  simpa only [spanningChild] using
    Classical.choose_spec (exists_spanning_part s I hI C hL hR hs)

/-- Every consecutive core interval strictly spanning s is that same actual part. -/
theorem spanningChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K) (hk : K.left < s ∧ s < K.right) :
    K = spanningChild s I hI C hL hR hs := by
  have hc : C.toComposition.cutSet.Consecutive K := by
    simpa only [BoundaryCutSet.toComposition_cutSet] using hK
  obtain ⟨k, he⟩ := C.toComposition.exists_part_of_consecutive K hc
  have hks : (C.toComposition.part k).left < s ∧ s < (C.toComposition.part k).right := by
    simpa only [he] using hk
  have hi := C.toComposition.part_interior_unique s hks
    (Classical.choose_spec (exists_spanning_part s I hI C hL hR hs))
  change K = C.toComposition.part (Classical.choose (exists_spanning_part s I hI C hL hR hs))
  exact he.symm.trans (congrArg C.toComposition.part hi)

/-- Every other actual core child lies strictly on one side of the missing cut. -/
theorem spanningChild_other (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningChild s I hI C hL hR hs) : K.right < s ∨ s < K.left := by
  have hleft : K.left ≠ s := by
    intro he
    exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hK.1)
  have hright : K.right ≠ s := by
    intro he
    exact hs ((congrArg (fun q : Fin n => q ∈ C.cuts) he).mp hK.2.1)
  by_cases hr : K.right < s
  · exact Or.inl hr
  · right
    have hsr : s < K.right := lt_of_le_of_ne (le_of_not_gt hr) hright.symm
    have hn : ¬ K.left < s := by
      intro hl
      exact hne (spanningChild_unique s I hI C hL hR hs K hK ⟨hl, hsr⟩)
    exact lt_of_le_of_ne (le_of_not_gt hn) hleft.symm

/-- The distinguished expanded child strictly contains both physical duplicate positions. -/
theorem emptySpanning_spanningChild_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s)
      (spanningChild s I hI C hL hR hs)).left < A s ∧
    B s < (OrderedBoundaryTransport.interval (startingOldEmbedding s)
      (spanningChild s I hI C hL hR hs)).right := by
  have hb := spanningChild_bounds s I hI C hL hR hs
  constructor
  · change old s (spanningChild s I hI C hL hR hs).left < A s
    exact lt_of_lt_of_eq (old_strictMono s hb.1) (old_self s)
  · exact starting_B_lt_old s _ hb.2

theorem emptySpanning_otherChild_bounds (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningChild s I hI C hL hR hs) :
    (OrderedBoundaryTransport.interval (startingOldEmbedding s) K).right < A s ∨
      B s < (OrderedBoundaryTransport.interval (startingOldEmbedding s) K).left := by
  rcases spanningChild_other s I hI C hL hR hs K hK hne with hr | hl
  · left
    change old s K.right < A s
    exact lt_of_lt_of_eq (old_strictMono s hr) (old_self s)
  · exact Or.inr (starting_B_lt_old s K.left hl)

theorem emptySpanning_spanningChild_consecutive (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts) :
    (emptySpanningCutSet s I hI C hs).Consecutive
      (OrderedBoundaryTransport.interval (startingOldEmbedding s)
        (spanningChild s I hI C hL hR hs)) :=
  (consecutive_ordered_image_iff (startingOldEmbedding s) C (emptySpanningCutSet s I hI C hs)
    (emptySpanningCutSet_cuts s I hI C hs) _).mpr (spanningChild_consecutive s I hI C hL hR hs)

/-- This is an exhaustive statement about the actual expanded child domain. -/
theorem emptySpanning_child_trichotomy (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (emptySpanningCutSet s I hI C hs).Consecutive J) :
    J = OrderedBoundaryTransport.interval (startingOldEmbedding s)
        (spanningChild s I hI C hL hR hs) ∨ J.right < A s ∨ B s < J.left := by
  obtain ⟨K, hK, he⟩ := consecutive_ordered_image_exhaust (startingOldEmbedding s) C
    (emptySpanningCutSet s I hI C hs) (emptySpanningCutSet_cuts s I hI C hs) J hJ
  by_cases hk : K = spanningChild s I hI C hL hR hs
  · exact Or.inl (he.symm.trans (congrArg (OrderedBoundaryTransport.interval (startingOldEmbedding s)) hk))
  · right
    have hb := emptySpanning_otherChild_bounds s I hI C hL hR hs K hK hk
    simpa only [he] using hb

theorem emptySpanning_spanningChild_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (J : BoundaryInterval (n + 1)) (hJ : (emptySpanningCutSet s I hI C hs).Consecutive J)
    (hj : J.left < A s ∧ B s < J.right) :
    J = OrderedBoundaryTransport.interval (startingOldEmbedding s)
      (spanningChild s I hI C hL hR hs) := by
  rcases emptySpanning_child_trichotomy s I hI C hL hR hs J hJ with he | hr | hl
  · exact he
  · exact False.elim (lt_asymm (lt_trans (A_lt_B s) hj.2) hr)
  · exact False.elim (lt_asymm (lt_trans hj.1 (A_lt_B s)) hl)

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The concrete old section recovers both strictly spanning endpoints. -/
theorem emptySpanning_old_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right) :
    old s (collapseInterval s I hI).left = I.left ∧
      old s (collapseInterval s I hI).right = I.right :=
  ⟨old_collapse_of_ne_B s I.left (ne_of_lt (lt_trans hL (A_lt_B s))),
    old_collapse_of_ne_B s I.right (ne_of_gt hR)⟩

theorem emptySpanning_interior (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) :
    (emptySpanningCutSet s I hI C hs).interior.val = C.interior.val.image (old s) := by
  have he := emptySpanning_old_endpoints s I hI hL hR
  ext p
  constructor
  · intro hp
    obtain ⟨hpc, hpl, hpr⟩ := (starting_mem_interior_iff _ p).mp hp
    rw [emptySpanningCutSet_cuts] at hpc
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
    · rw [emptySpanningCutSet_cuts]
      exact Finset.mem_image.mpr ⟨k, hkc, rfl⟩
    · exact lt_of_eq_of_lt he.1.symm (old_strictMono s hkl)
    · exact lt_of_lt_of_eq (old_strictMono s hkr) he.2


def emptySpanningInteriorMap (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    {p : Fin (n + 1) // p ∈ (emptySpanningCutSet s I hI C hs).interior.val} :=
  ⟨old s x.val, by
    rw [emptySpanning_interior s I hI C hs hL hR]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩

/-- The actual old-position map, with every core interior cut represented once. -/
def emptySpanningInteriorEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) :
    {k : Fin n // k ∈ C.interior.val} ≃
      {p : Fin (n + 1) // p ∈ (emptySpanningCutSet s I hI C hs).interior.val} :=
  Equiv.ofBijective (emptySpanningInteriorMap s I hI C hs hL hR) ⟨by
    intro x y he
    apply Subtype.ext
    exact old_injective s (congrArg Subtype.val he), by
    intro p
    have hp : p.val ∈ C.interior.val.image (old s) :=
      Eq.mp (congrArg (fun S : Finset (Fin (n + 1)) => p.val ∈ S)
        (emptySpanning_interior s I hI C hs hL hR)) p.property
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩⟩

@[simp]
theorem emptySpanningInteriorEquiv_val (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    ((emptySpanningInteriorEquiv s I hI C hs hL hR) x).val = old s x.val := rfl


theorem emptySpanning_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (emptySpanningCutSet s I hI C hs).nearAtCut
        ((emptySpanningInteriorEquiv s I hI C hs hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.nearAtCut x) := by
  let S := emptySpanningCutSet s I hI C hs
  let y := (emptySpanningInteriorEquiv s I hI C hs hL hR) x
  have hl := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (emptySpanningCutSet_cuts s I hI C hs) (C.nearLeftInterval x)).mpr
      (C.nearLeftInterval_consecutive x)
  have hr := (consecutive_ordered_image_iff (startingOldEmbedding s) C S
    (emptySpanningCutSet_cuts s I hI C hs) (C.nearRightInterval x)).mpr
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

theorem emptySpanning_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right)
    (x : {k : Fin n // k ∈ C.interior.val}) :
    (emptySpanningCutSet s I hI C hs).farAtCut
        ((emptySpanningInteriorEquiv s I hI C hs hL hR) x) =
      OrderedBoundaryTransport.triple (startingOldEmbedding s) (C.farAtCut x) := by
  have he := emptySpanning_old_endpoints s I hI hL hR
  apply IncreasingBoundaryTriple.eq_of_entries
  · exact he.1.symm
  · change ((emptySpanningCutSet s I hI C hs).farAtCut
        ((emptySpanningInteriorEquiv s I hI C hs hL hR) x)).middle =
      old s (C.farAtCut x).middle
    rw [BoundaryCutSet.farAtCut_middle, C.farAtCut_middle]
    rfl
  · exact he.2.symm


theorem emptySpanning_gate_values (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (x : {x : Fin n // x ∈ C.interior.val}) :
    tripleLift s D0 tD ((emptySpanningCutSet s I hI C hs).nearAtCut
      (emptySpanningInteriorEquiv s I hI C hs hL hR x)) = D0 (C.nearAtCut x) ∧
    tripleLift s H0 tH ((emptySpanningCutSet s I hI C hs).farAtCut
      (emptySpanningInteriorEquiv s I hI C hs hL hR x)) = H0 (C.farAtCut x) := by
  constructor
  · rw [emptySpanning_nearTriple, tripleLift_startingOld]
  · rw [emptySpanning_farTriple, tripleLift_startingOld]


theorem emptySpanning_gate_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hs : s ∉ C.cuts) (hL : I.left < A s) (hR : B s < I.right) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) :
    cutGateProduct (emptySpanningCutSet s I hI C hs)
      (tripleLift s D0 tD) (tripleLift s H0 tH) = cutGateProduct C D0 H0 := by
  unfold cutGateProduct
  symm
  apply Fintype.prod_equiv (emptySpanningInteriorEquiv s I hI C hs hL hR)
  intro x
  have h := emptySpanning_gate_values s I hI C hs hL hR D0 H0 tD tH x
  rw [h.1, h.2]


end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

theorem avoiding_not_duplicate (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) : I ≠ duplicateInterval s := by
  intro he
  subst I
  exact havoid ⟨le_rfl, le_rfl⟩

/-- Collapse is injective on the entire closed vertex interval whenever
that interval does not contain both duplicate occurrences. -/
theorem collapse_injective_on_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    {p q : Fin (n + 1)} (hp : I.left ≤ p ∧ p ≤ I.right)
    (hq : I.left ≤ q ∧ q ≤ I.right) (he : collapse s p = collapse s q) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · obtain ⟨hpa, hqb⟩ := (collapse_eq_iff_of_lt s p q h).mp he
    exact False.elim (havoid ⟨hpa ▸ hp.1, hqb ▸ hq.2⟩)
  · exact h
  · obtain ⟨hqa, hpb⟩ := (collapse_eq_iff_of_lt s q p h).mp he.symm
    exact False.elim (havoid ⟨hqa ▸ hq.1, hpb ▸ hp.2⟩)

/-- The unique avoiding presentation is the full preimage inside I.
This formula also handles an interval ending at A or starting at B. -/
def avoidingExpandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    BoundaryCutSet I where
  cuts := Finset.univ.filter (fun p => (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts)
  left_mem := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨⟨le_rfl, I.increasing.le⟩, C.left_mem⟩⟩
  right_mem := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨⟨I.increasing.le, le_rfl⟩, C.right_mem⟩⟩
  bounds := by intro p hp; exact (Finset.mem_filter.mp hp).2.1

theorem mem_avoidingExpandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (p : Fin (n + 1)) : p ∈ (avoidingExpandCuts s I hI C).cuts ↔
      (I.left ≤ p ∧ p ≤ I.right) ∧ collapse s p ∈ C.cuts := by
  simp only [avoidingExpandCuts, Finset.mem_filter, Finset.mem_univ, true_and]

theorem collapse_avoidingExpandCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    collapseCuts s I hI (avoidingExpandCuts s I hI C) = C := by
  apply BoundaryCutSet.ext
  ext k
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ((mem_avoidingExpandCuts s I hI C p).mp hp).2
  · intro hk
    obtain ⟨p, hpb, hpc⟩ := exists_position_in_interval s I k (C.bounds k hk)
    exact Finset.mem_image.mpr ⟨p,
      (mem_avoidingExpandCuts s I hI C p).mpr ⟨hpb, hpc.symm ▸ hk⟩, hpc⟩

theorem avoidingExpandCuts_collapse (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (T : BoundaryCutSet I) : avoidingExpandCuts s I hI (collapseCuts s I hI T) = T := by
  apply BoundaryCutSet.ext
  ext p
  constructor
  · intro hp
    obtain ⟨hpb, hpc⟩ := (mem_avoidingExpandCuts s I hI _ p).mp hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hpc
    have hqp := collapse_injective_on_avoiding s I havoid (T.bounds q hq) hpb he
    exact hqp ▸ hq
  · intro hp
    exact (mem_avoidingExpandCuts s I hI _ p).mpr
      ⟨T.bounds p hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

/-- An actual inverse equivalence, not an equality of cut-set cardinalities. -/
def avoidingCutSetEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    BoundaryCutSet I ≃ BoundaryCutSet (collapseInterval s I hI) where
  toFun := collapseCuts s I hI
  invFun := avoidingExpandCuts s I hI
  left_inv := avoidingExpandCuts_collapse s I hI havoid
  right_inv := collapse_avoidingExpandCuts s I hI

/-- All raw compositions, including unary, survive the avoiding collapse. -/
def avoidingCompositionEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    IntervalComposition I ≃ IntervalComposition (collapseInterval s I hI) :=
  ((IntervalComposition.cutSetEquiv I).trans (avoidingCutSetEquiv s I hI havoid)).trans
    (IntervalComposition.cutSetEquiv (collapseInterval s I hI)).symm

/-- The actual local subset of the full-preimage presentation. -/
def avoidingLocalCuts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI)) :
    CutFiber s I hI C :=
  ⟨(localCuts s I hI (avoidingExpandCuts s I hI C)).val, by
    have h := (localCuts s I hI (avoidingExpandCuts s I hI C)).property
    simpa only [collapse_avoidingExpandCuts] using h⟩

/-- Every admissible local selection gives the same avoiding presentation. -/
theorem expandCuts_eq_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) (Q : CutFiber s I hI C) :
    expandCuts s I hI C Q = avoidingExpandCuts s I hI C := by
  have h := avoidingExpandCuts_collapse s I hI havoid (expandCuts s I hI C Q)
  rw [collapse_expandCuts] at h
  exact h.symm

theorem avoidingCutFiber_unique (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) (Q : CutFiber s I hI C) :
    Q = avoidingLocalCuts s I hI C := by
  apply Subtype.ext
  calc
    Q.val = (localCuts s I hI (expandCuts s I hI C Q)).val :=
      (localCuts_expandCuts_val s I hI C Q).symm
    _ = (localCuts s I hI (avoidingExpandCuts s I hI C)).val := by
      rw [expandCuts_eq_avoiding s I hI havoid C Q]
    _ = (avoidingLocalCuts s I hI C).val := rfl

def avoidingCutFiberEquiv (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) : PUnit ≃ CutFiber s I hI C :=
  Equiv.ofBijective (fun _ => avoidingLocalCuts s I hI C) ⟨by
    intro x y _
    exact Subsingleton.elim x y, by
    intro Q
    exact ⟨PUnit.unit, (avoidingCutFiber_unique s I hI havoid C Q).symm⟩⟩

/-- The inner fibre sum has exactly the one full-preimage summand. -/
theorem sum_avoidingCutFiber {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (C : BoundaryCutSet (collapseInterval s I hI)) (f : BoundaryCutSet I → R) :
    (∑ Q : CutFiber s I hI C, f (expandCuts s I hI C Q)) = f (avoidingExpandCuts s I hI C) := by
  have he := (Fintype.sum_equiv (avoidingCutFiberEquiv s I hI havoid C)
    (fun _ : Unit => f (avoidingExpandCuts s I hI C))
    (fun Q => f (expandCuts s I hI C Q))
    (fun _ : Unit => congrArg f (expandCuts_eq_avoiding s I hI havoid C _).symm)).symm
  simpa using he

local instance avoidingCutSetFintype {m : ℕ} [NeZero m] (I : BoundaryInterval m) :
    Fintype (BoundaryCutSet I) :=
  Fintype.ofEquiv (IntervalComposition I) (IntervalComposition.cutSetEquiv I)

theorem sum_avoidingCuts {R : Type*} [AddCommMonoid R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (f : BoundaryCutSet I → R) :
    (∑ T : BoundaryCutSet I, f T) =
      ∑ C : BoundaryCutSet (collapseInterval s I hI), f (avoidingExpandCuts s I hI C) :=
  Fintype.sum_equiv (avoidingCutSetEquiv s I hI havoid) _ _
    (fun T => congrArg f (avoidingExpandCuts_collapse s I hI havoid T).symm)

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Collapse every actual cut in an avoiding interval, retaining the part
count. Strictness is derived on the closed parent interval, not supplied. -/
def collapseComposition (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    IntervalComposition (collapseInterval s I hI) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => collapse s (π.cut k)
  strict := by
    intro a b hab
    have bounds (k : Fin (π.parts + 1)) : I.left ≤ π.cut k ∧ π.cut k ≤ I.right := by
      constructor
      · rw [← π.first]
        exact π.strict.monotone (Fin.zero_le k)
      · rw [← π.last]
        exact π.strict.monotone (Fin.le_last k)
    apply lt_of_le_of_ne (collapse_monotone s (π.strict hab).le)
    intro he
    exact (ne_of_lt (π.strict hab))
      (collapse_injective_on_avoiding s I havoid (bounds a) (bounds b) he)
  first := congrArg (collapse s) π.first
  last := congrArg (collapse s) π.last

@[simp] theorem collapseComposition_parts (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    (collapseComposition s I hI havoid π).parts = π.parts := rfl

@[simp] theorem collapseComposition_cut (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts + 1)) :
    (collapseComposition s I hI havoid π).cut k = collapse s (π.cut k) := rfl

theorem collapseComposition_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    (collapseComposition s I hI havoid π).cut 0 = collapse s I.left ∧
    (collapseComposition s I hI havoid π).cut (Fin.last π.parts) = collapse s I.right :=
  ⟨congrArg (collapse s) π.first, congrArg (collapse s) π.last⟩

/-- The direct map has precisely the actual collapsed complete cut set. -/
theorem collapseComposition_cutSet (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    (collapseComposition s I hI havoid π).cutSet = collapseCuts s I hI π.cutSet := by
  apply BoundaryCutSet.ext
  change Finset.univ.image (fun k => collapse s (π.cut k)) =
    (Finset.univ.image π.cut).image (collapse s)
  rw [Finset.image_image]
  rfl

/-- The direct pointwise collapse is the previously constructed genuine
composition equivalence, proved by the complete cut set, not endpoints. -/
theorem collapseComposition_eq_avoidingCompositionEquiv (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I) :
    collapseComposition s I hI havoid π = (avoidingCompositionEquiv s I hI havoid) π := by
  apply IntervalComposition.cutSet_injective
  rw [collapseComposition_cutSet]
  change collapseCuts s I hI π.cutSet =
    (collapseCuts s I hI π.cutSet).toComposition.cutSet
  exact (BoundaryCutSet.toComposition_cutSet _).symm

theorem collapseComposition_part_endpoints (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin π.parts) :
    ((collapseComposition s I hI havoid π).part k).left = collapse s (π.part k).left ∧
    ((collapseComposition s I hI havoid π).part k).right = collapse s (π.part k).right :=
  ⟨rfl, rfl⟩

/-- Every actual part of an avoiding composition remains avoiding. -/
theorem composition_part_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin π.parts) : ¬ ((π.part k).left ≤ A s ∧ B s ≤ (π.part k).right) := by
  intro h
  have hb := π.part_bounds k
  exact havoid ⟨le_trans hb.1 h.1, le_trans h.2 hb.2⟩

/-- The mapped child is the actual collapsed child interval; its distinct
endpoints are derived from the proved child avoidance. -/
theorem collapseComposition_part (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin π.parts) :
    (collapseComposition s I hI havoid π).part k =
      collapseInterval s (π.part k)
        (avoiding_not_duplicate s (π.part k) (composition_part_avoiding s I havoid π k)) := rfl

theorem collapseComposition_nearTriple_positions (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) :
    ((collapseComposition s I hI havoid π).nearTriple k).lower =
        collapse s (π.nearTriple k).lower ∧
    ((collapseComposition s I hI havoid π).nearTriple k).middle =
        collapse s (π.nearTriple k).middle ∧
    ((collapseComposition s I hI havoid π).nearTriple k).upper =
        collapse s (π.nearTriple k).upper := ⟨rfl, rfl, rfl⟩

theorem collapseComposition_farTriple_positions (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) :
    ((collapseComposition s I hI havoid π).farTriple k).lower =
        collapse s (π.farTriple k).lower ∧
    ((collapseComposition s I hI havoid π).farTriple k).middle =
        collapse s (π.farTriple k).middle ∧
    ((collapseComposition s I hI havoid π).farTriple k).upper =
        collapse s (π.farTriple k).upper := ⟨rfl, rfl, rfl⟩

/-- Every bounded triple in the avoiding interval is a plain triple. -/
theorem triple_plain_of_avoiding_interval (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (T : IncreasingBoundaryTriple (n + 1)) (hL : I.left ≤ T.lower)
    (hR : T.upper ≤ I.right) : ¬ tripleContainsBoth s T := by
  intro h
  apply havoid
  rcases (triple_contains_both_iff s T).mp h with hu | hl
  · constructor
    · calc
        I.left ≤ T.lower := hL
        _ ≤ T.middle := T.lower_middle.le
        _ = A s := hu.1
    · calc
        B s = T.upper := hu.2.symm
        _ ≤ I.right := hR
  · constructor
    · calc
        I.left ≤ T.lower := hL
        _ = A s := hl.1
    · calc
        B s = T.middle := hl.2.symm
        _ ≤ T.upper := T.middle_upper.le
        _ ≤ I.right := hR

theorem nearTriple_plain_of_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) : ¬ tripleContainsBoth s (π.nearTriple k) := by
  apply triple_plain_of_avoiding_interval s I havoid
  · change I.left ≤ π.cut ⟨k.val, by have := k.isLt; omega⟩
    rw [← π.first]
    exact π.strict.monotone (Fin.zero_le _)
  · change π.cut ⟨k.val + 2, by have := k.isLt; omega⟩ ≤ I.right
    rw [← π.last]
    exact π.strict.monotone (Fin.le_last _)

theorem farTriple_plain_of_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) : ¬ tripleContainsBoth s (π.farTriple k) :=
  triple_plain_of_avoiding_interval s I havoid (π.farTriple k) le_rfl le_rfl

/-- Compatibility with any proof of plainness, including the preceding
derived one. Proof irrelevance leaves the actual collapsed positions fixed. -/
theorem collapseComposition_nearTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) (hplain : ¬ tripleContainsBoth s (π.nearTriple k)) :
    (collapseComposition s I hI havoid π).nearTriple k =
      collapseTriple s (π.nearTriple k) hplain := rfl

theorem collapseComposition_farTriple (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (π : IntervalComposition I)
    (k : Fin (π.parts - 1)) (hplain : ¬ tripleContainsBoth s (π.farTriple k)) :
    (collapseComposition s I hI havoid π).farTriple k =
      collapseTriple s (π.farTriple k) hplain := rfl

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ}

/-- Avoiding the consecutive pair means lying entirely on one of its two sides.
Both an interval ending at A and an interval starting at B are included. -/
theorem avoiding_interval_side_iff (s : Fin n) (I : BoundaryInterval (n + 1)) :
    (¬ (I.left ≤ A s ∧ B s ≤ I.right)) ↔ I.right ≤ A s ∨ B s ≤ I.left := by
  change (¬ (I.left.val ≤ s.val ∧ s.val + 1 ≤ I.right.val)) ↔
    I.right.val ≤ s.val ∨ s.val + 1 ≤ I.left.val
  have hi : I.left.val < I.right.val := I.increasing
  omega

/-- On an avoiding interval collapse subtracts the same amount from both
endpoints, so it preserves the actual number of leaves. -/
theorem collapseInterval_leaves_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    (collapseInterval s I hI).leaves = I.leaves := by
  have hi : I.left.val < I.right.val := I.increasing
  change (collapse s I.right).val - (collapse s I.left).val = I.right.val - I.left.val
  rw [collapse_val, collapse_val]
  rcases (avoiding_interval_side_iff s I).mp havoid with hr | hl
  · have hrv : I.right.val ≤ s.val := hr
    have hlv : I.left.val ≤ s.val := by omega
    rw [if_pos hrv, if_pos hlv]
  · have hlv : s.val + 1 ≤ I.left.val := hl
    have hln : ¬ I.left.val ≤ s.val := by omega
    have hrn : ¬ I.right.val ≤ s.val := by omega
    rw [if_neg hrn, if_neg hln]
    omega

/-- The required unit coordinate survives the actual avoiding collapse. -/
theorem collapseInterval_unit_avoiding {R : Type*} [CommRing R]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) :
    boundaryUnitArray (R := R) (collapseInterval s I hI) = boundaryUnitArray (R := R) I := by
  have hl := collapseInterval_leaves_avoiding s I hI havoid
  have hp : I.left.val < I.right.val := I.increasing
  have hc : (collapseInterval s I hI).left.val < (collapseInterval s I hI).right.val :=
    (collapseInterval s I hI).increasing
  unfold BoundaryInterval.leaves at hl
  have he : (collapseInterval s I hI).right.val = (collapseInterval s I hI).left.val + 1 ↔
      I.right.val = I.left.val + 1 := by omega
  simp only [boundaryUnitArray, he]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Every near and far gate is transported at its actual collapsed triple.
No sign-square or nonzero assumption is needed in an avoiding interval. -/
theorem nearFarWeight_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (π : IntervalComposition I) (D0 H0 : TripleArray n ℚ) (tD tH : Fin n → ℚ) :
    π.nearFarWeight (tripleLift s D0 tD) (tripleLift s H0 tH) =
      (collapseComposition s I hI havoid π).nearFarWeight D0 H0 := by
  change (∏ k : Fin (π.parts - 1),
    (tripleLift s D0 tD (π.nearTriple k) - tripleLift s H0 tH (π.farTriple k)) * ⅟ (2 : ℚ)) =
      ∏ k : Fin (π.parts - 1),
        (D0 ((collapseComposition s I hI havoid π).nearTriple k) -
          H0 ((collapseComposition s I hI havoid π).farTriple k)) * ⅟ (2 : ℚ)
  apply Finset.prod_congr rfl
  intro k hk
  have hn := nearTriple_plain_of_avoiding s I havoid π k
  have hf := farTriple_plain_of_avoiding s I havoid π k
  rw [tripleLift_plain s D0 tD _ hn, tripleLift_plain s H0 tH _ hf,
    collapseComposition_nearTriple s I hI havoid π k hn,
    collapseComposition_farTriple s I hI havoid π k hf]

/-- The proposed ordinary array reads the exact collapsed child, including
children ending at A or starting at B. Their avoidance is derived from I. -/
theorem ordinaryLift_child_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (π : IntervalComposition I) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) (k : Fin π.parts) :
    ordinaryLift s etaMinus etaPlus t b0 (π.part k) =
      b0 ((collapseComposition s I hI havoid π).part k) := by
  have hpart := composition_part_avoiding s I havoid π k
  rw [collapseComposition_part s I hI havoid π k,
    ordinaryLift_plain s etaMinus etaPlus t b0 (π.part k) hpart]

/-- Transport the complete child product without cancellation of any factor. -/
theorem ordinaryLift_children_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (π : IntervalComposition I) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    (∏ k : Fin π.parts, ordinaryLift s etaMinus etaPlus t b0 (π.part k)) =
      ∏ k : Fin (collapseComposition s I hI havoid π).parts,
        b0 ((collapseComposition s I hI havoid π).part k) := by
  change (∏ k : Fin π.parts, ordinaryLift s etaMinus etaPlus t b0 (π.part k)) =
    ∏ k : Fin π.parts, b0 ((collapseComposition s I hI havoid π).part k)
  apply Finset.prod_congr rfl
  intro k hk
  exact ordinaryLift_child_avoiding s I hI havoid π etaMinus etaPlus t b0 k

/-- The actual complete avoiding transform equals its core transform.
The reindexing is the proved composition equivalence and includes unary terms. -/
theorem nearFarTransform_ordinaryLift_avoiding (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 tD) (tripleLift s H0 tH)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      nearFarTransform D0 H0 b0 (collapseInterval s I hI) := by
  unfold nearFarTransform
  apply Fintype.sum_equiv (avoidingCompositionEquiv s I hI havoid)
  intro π
  rw [← collapseComposition_eq_avoidingCompositionEquiv s I hI havoid π,
    nearFarWeight_avoiding s I hI havoid π D0 H0 tD tH,
    ordinaryLift_children_avoiding s I hI havoid π etaMinus etaPlus t b0]

/-- With the core ordinary array defined by the actual triangular inverse,
every avoiding parent coordinate satisfies its required unit equation. -/
theorem ordinaryLift_equation_avoiding (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right))
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) :
    nearFarTransform (parentNear s t) (tripleLift s H0 t)
      (ordinaryLift s etaMinus etaPlus t (nearFarInverse (coreNear s t) H0 boundaryUnitArray)) I =
      boundaryUnitArray I := by
  unfold parentNear
  rw [nearFarTransform_ordinaryLift_avoiding s I hI havoid,
    nearFarTransform_inverse, collapseInterval_unit_avoiding s I hI havoid]

/-- Negating every far datum commutes with the complete plain/exceptional lift. -/
theorem tripleLift_neg {R : Type*} [Neg R] (s : Fin n)
    (H0 : TripleArray n R) (t : Fin n → R) :
    tripleLift s (-H0) (-t) = -(tripleLift s H0 t) := by
  funext T
  change tripleLift s (-H0) (-t) T = -(tripleLift s H0 t T)
  unfold tripleLift
  split_ifs <;> rfl

/-- The root-sign transform also transports completely on an avoiding interval.
This follows from the same actual summand correspondence, not a near-array
independence assertion about individual open sums. -/
theorem rootTransform_ordinaryLift_avoiding (s : Fin n)
    (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (havoid : ¬ (I.left ≤ A s ∧ B s ≤ I.right)) (D0 H0 : TripleArray n ℚ)
    (tD tH : Fin n → ℚ) (etaMinus etaPlus : ℚ) (t : Fin n → ℚ)
    (b0 : IntervalArray n ℚ) :
    nearFarTransform (tripleLift s D0 tD) (-(tripleLift s H0 tH))
      (ordinaryLift s etaMinus etaPlus t b0) I =
      nearFarTransform D0 (-H0) b0 (collapseInterval s I hI) := by
  rw [← tripleLift_neg s H0 tH]
  exact nearFarTransform_ordinaryLift_avoiding s I hI havoid D0 (-H0) tD (-tH)
    etaMinus etaPlus t b0

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The unique actual core child containing s receives the spanning multiplier. -/
theorem emptySpanning_distinguished_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) (spanningChild s I hI C hL hR hs)) =
      ((etaMinus + etaPlus) / 2) * b0 (spanningChild s I hI C hL hR hs) := by
  let K := spanningChild s I hI C hL hR hs
  have hb := spanningChild_bounds s I hI C hL hR hs
  have hl : old s K.left < A s := by
    rw [← old_self s]
    exact old_strictMono s hb.1
  have hr : B s < old s K.right := by
    have hk : s.val < K.right.val := hb.2
    change s.val + 1 < (old s K.right).val
    rw [old_val, if_neg (by omega)]
    omega
  rw [ordinaryLift_span s etaMinus etaPlus t b0 _ hl hr,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Every other actual child lies strictly to one side and contributes its core value. -/
theorem emptySpanning_other_child_factor (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (K : BoundaryInterval n) (hK : C.Consecutive K)
    (hne : K ≠ spanningChild s I hI C hL hR hs) :
    ordinaryLift s etaMinus etaPlus t b0
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) = b0 K := by
  have hplain : ¬ intervalContainsBoth s
      (OrderedBoundaryTransport.interval (startingOldEmbedding s) K) := by
    rcases spanningChild_other s I hI C hL hR hs K hK hne with hr | hl
    · have ha : old s K.right < A s := by
        rw [← old_self s]
        exact old_strictMono s hr
      exact fun h => (not_le_of_gt (lt_trans ha (A_lt_B s))) h.2
    · have ha : A s < old s K.left := by
        rw [← old_self s]
        exact old_strictMono s hl
      exact fun h => (not_le_of_gt ha) h.1
  rw [ordinaryLift_plain s etaMinus etaPlus t b0 _ hplain,
    collapse_sectionInterval s (startingOldEmbedding s) (collapse_old s)]

/-- Reindex the actual full child product and isolate one multiplier without division. -/
theorem emptySpanning_child_product (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (etaMinus etaPlus : ℚ) (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∏ J : {J : BoundaryInterval (n + 1) //
        (emptySpanningCutSet s I hI C hs).Consecutive J},
      ordinaryLift s etaMinus etaPlus t b0 J.val) =
      ((etaMinus + etaPlus) / 2) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := by
  let K0 : {K : BoundaryInterval n // C.Consecutive K} :=
    ⟨spanningChild s I hI C hL hR hs, spanningChild_consecutive s I hI C hL hR hs⟩
  let m : ℚ := (etaMinus + etaPlus) / 2
  calc
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        ordinaryLift s etaMinus etaPlus t b0
          (OrderedBoundaryTransport.interval (startingOldEmbedding s) K.val) :=
      (Fintype.prod_equiv (emptySpanningChildrenEquiv s I hI C hs) _ _ (fun _ => rfl)).symm
    _ = ∏ K : {K : BoundaryInterval n // C.Consecutive K},
        (if K = K0 then m else 1) * b0 K.val := by
      apply Finset.prod_congr rfl
      intro K hK
      by_cases he : K = K0
      · subst K
        rw [if_pos rfl]
        exact emptySpanning_distinguished_child_factor s I hI C hL hR hs etaMinus etaPlus t b0
      · rw [if_neg he, one_mul]
        exact emptySpanning_other_child_factor s I hI C hL hR hs etaMinus etaPlus t b0 K.val K.property
          (fun h => he (Subtype.ext h))
    _ = (∏ K : {K : BoundaryInterval n // C.Consecutive K}, if K = K0 then m else 1) *
        ∏ K : {K : BoundaryInterval n // C.Consecutive K}, b0 K.val := Finset.prod_mul_distrib
    _ = _ := by simp [m]

/-- The unique no-cut presentation has its complete core summand multiplied by k. -/
theorem emptySpanning_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (emptySpanningCutSet s I hI C hs).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct,
    emptySpanning_gate_product s I hI C hs hL hR,
    emptySpanning_child_product s I hI C hL hR hs, nearFarSummand_eq_cutGateProduct]
  ring

/-- Sum over the actual singleton fiber, including a unary core composition. -/
theorem emptySpanning_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand D0 H0 b0 := by
  rw [sum_emptyCutFiber s I hI C hs]
  exact emptySpanning_summand s I hI C hL hR hs D0 H0 etaMinus etaPlus t u b0

/-- Reversing the complete far array preserves the no-cut multiplier and ordinary children. -/
theorem emptySpanning_root_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∉ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s D0 t) (-tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand D0 (-H0) b0 := by
  rw [← tripleLift_neg]
  exact emptySpanning_weighted_fiber_sum s I hI C hL hR hs D0 (-H0) etaMinus etaPlus t (-u) b0

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The actual complete near/far transform reindexed by the proved physical
composition fibers. All gates and child products remain in each summand. -/
theorem nearFarTransform_eq_cutFiber_sum {R : Type*} [CommRing R] [Invertible (2 : R)]
    (s : Fin n) (I : BoundaryInterval (n + 1)) (hI : I ≠ duplicateInterval s)
    (D H : TripleArray (n + 1) R) (X : IntervalArray (n + 1) R) :
    nearFarTransform D H X I =
      ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand D H X := by
  rw [nearFarTransform_eq_cutSet_sum]
  exact sum_cutFiber s I hI (fun T => T.nearFarSummand D H X)

/-- The proposed source ordinary array satisfies the singleton coordinate
for arbitrary top arrays, including both ordinary and reversed-far tops.
This is an interval identity, not a two-gon polygon amplitude. -/
theorem ordinaryLift_transform_duplicate (s : Fin n) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) (D H : TripleArray (n + 1) ℚ) :
    nearFarTransform D H (ordinaryLift s etaMinus etaPlus t b0) (duplicateInterval s) = 1 := by
  rw [nearFarTransform_leaf D H _ _ (duplicateInterval_leaves s), ordinaryLift_duplicate]

/-- At the exceptional singleton interval the full ordinary equation is
already checked, before any use of inverse uniqueness for other coordinates. -/
theorem ordinaryLift_equation_duplicate (s : Fin n) (etaMinus etaPlus : ℚ)
    (t : Fin n → ℚ) (b0 : IntervalArray n ℚ) (D H : TripleArray (n + 1) ℚ) :
    nearFarTransform D H (ordinaryLift s etaMinus etaPlus t b0) (duplicateInterval s) =
      boundaryUnitArray (R := ℚ) (duplicateInterval s) := by
  rw [ordinaryLift_transform_duplicate, boundaryUnitArray_leaf _ (duplicateInterval_leaves s)]

end
end SM.SoftDuplication


namespace SM.SoftDuplication

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- The A-only row retains all core gates and receives the actual right-child multiplier. -/
theorem spanning_zero_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (spanningCutSet s I hI C hL hR hs 0).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaPlus - t (spanningRightNeighbor s I hI C hL hR hs)) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, spanning_zero_gate_product,
    spanning_zero_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- The B-only row retains all core gates and receives the actual left-child multiplier. -/
theorem spanning_one_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (D0 H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (spanningCutSet s I hI C hL hR hs 1).nearFarSummand
      (tripleLift s D0 t) (tripleLift s H0 u) (ordinaryLift s etaMinus etaPlus t b0) =
      ((etaMinus - t (spanningLeftNeighbor s I hI C hL hR hs)) / 2) *
        C.nearFarSummand D0 H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, spanning_one_gate_product,
    spanning_one_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- The both-cut row contributes exactly the new B gate; its singleton child has value one. -/
theorem spanning_two_summand (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ) :
    (spanningCutSet s I hI C hL hR hs 2).nearFarSummand
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) =
      ((t (spanningRightNeighbor s I hI C hL hR hs) -
        H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
        C.nearFarSummand (coreNear s t) H0 b0 := by
  rw [nearFarSummand_eq_cutGateProduct, spanning_two_gate_product,
    spanning_two_child_product, nearFarSummand_eq_cutGateProduct]
  ring

/-- Sum the complete actual three-row fiber. Its residual is a scalar times the
complete core summand, and the local square relation kills it with every exterior retained. -/
theorem spanning_cut_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right) (hs : s ∈ C.cuts)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hsq : (H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) ^ 2 =
      (t (spanningLeftNeighbor s I hI C hL hR hs)) ^ 2) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 := by
  rw [sum_spanningRows s I hI C hL hR hs]
  change (spanningCutSet s I hI C hL hR hs 0).nearFarSummand _ _ _ +
    (spanningCutSet s I hI C hL hR hs 1).nearFarSummand _ _ _ +
    (spanningCutSet s I hI C hL hR hs 2).nearFarSummand _ _ _ = _
  rw [spanning_zero_summand, spanning_one_summand, spanning_two_summand]
  calc
    _ = ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 -
        ((t (spanningLeftNeighbor s I hI C hL hR hs) +
          H0 (C.farAtCut (spanningCoreCut s I hI C hL hR hs))) / 2) *
          C.nearFarSummand (coreNear s t) H0 b0 := by ring
    _ = _ := by
      rw [spanning_core_summand_cancellation s I hI C hL hR hs H0 t b0 hsq, sub_zero]

/-- Every actual collapsed composition is included, whether or not it cuts at s.
Only off-s sign squares are used; the no-cut branch includes unary compositions. -/
theorem spanning_weighted_fiber_sum (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (C : BoundaryCutSet (collapseInterval s I hI))
    (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    (∑ Q : CutFiber s I hI C, (expandCuts s I hI C Q).nearFarSummand
      (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0)) =
      ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 := by
  by_cases hs : s ∈ C.cuts
  · exact spanning_cut_weighted_fiber_sum s I hI C hL hR hs H0 etaMinus etaPlus t u b0
      (spanning_core_far_square_of_signs s I hI C hL hR hs H0 t hH ht)
  · exact emptySpanning_weighted_fiber_sum s I hI C hL hR hs
      (coreNear s t) H0 etaMinus etaPlus t u b0

/-- Sum all actual fibers to obtain the complete strictly spanning transform.
No supplied solution or nonzero factor hypothesis enters this identity. -/
theorem nearFarTransform_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (tripleLift s (coreNear s t) t) (tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      ((etaMinus + etaPlus) / 2) *
        nearFarTransform (coreNear s t) H0 b0 (collapseInterval s I hI) := by
  rw [nearFarTransform_eq_cutFiber_sum s I hI, nearFarTransform_eq_cutSet_sum]
  calc
    _ = ∑ C : BoundaryCutSet (collapseInterval s I hI),
        ((etaMinus + etaPlus) / 2) * C.nearFarSummand (coreNear s t) H0 b0 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact spanning_weighted_fiber_sum s I hI C hL hR H0 etaMinus etaPlus t u b0 hH ht
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Reverse the whole far array while retaining the same ordinary child array.
The far square condition survives negation, and the spanning multiplier remains k. -/
theorem rootTransform_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (etaMinus etaPlus : ℚ)
    (t u : Fin n → ℚ) (b0 : IntervalArray n ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (tripleLift s (coreNear s t) t) (-tripleLift s H0 u)
      (ordinaryLift s etaMinus etaPlus t b0) I =
      ((etaMinus + etaPlus) / 2) *
        nearFarTransform (coreNear s t) (-H0) b0 (collapseInterval s I hI) := by
  rw [← tripleLift_neg s H0 u]
  apply nearFarTransform_spanning s I hI hL hR (-H0) etaMinus etaPlus t (-u) b0 ?_ ht
  intro T
  simpa only [Pi.neg_apply, neg_sq] using hH T

/-- A strictly spanning parent has more than one leaf, so its unit entry vanishes. -/
theorem boundaryUnitArray_spanning_zero (s : Fin n) (I : BoundaryInterval (n + 1))
    (hL : I.left < A s) (hR : B s < I.right) : boundaryUnitArray (R := ℚ) I = 0 := by
  have hl : I.left.val < s.val := hL
  have hr : s.val + 1 < I.right.val := hR
  have hn : I.right.val ≠ I.left.val + 1 := by omega
  simp only [boundaryUnitArray, if_neg hn]

/-- The actual collapsed spanning interval strictly contains s and also has a zero unit entry. -/
theorem boundaryUnitArray_core_spanning_zero (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right) :
    boundaryUnitArray (R := ℚ) (collapseInterval s I hI) = 0 := by
  have hb := span_collapsed_bounds s I hL hR
  have hl : (collapseInterval s I hI).left.val < s.val := hb.1
  have hr : s.val < (collapseInterval s I hI).right.val := hb.2
  have hn : (collapseInterval s I hI).right.val ≠
      (collapseInterval s I hI).left.val + 1 := by omega
  simp only [boundaryUnitArray, if_neg hn]

/-- The proposed ordinary array satisfies the actual spanning coordinate with
canonical core inverse and the actual cyclic-neighbor eta values. -/
theorem ordinaryLift_equation_spanning (s : Fin n) (I : BoundaryInterval (n + 1))
    (hI : I ≠ duplicateInterval s) (hL : I.left < A s) (hR : B s < I.right)
    (H0 : TripleArray n ℚ) (t : Fin n → ℚ)
    (hH : ∀ T, (H0 T) ^ 2 = 1) (ht : ∀ k, k ≠ s → (t k) ^ 2 = 1) :
    nearFarTransform (parentNear s t) (tripleLift s H0 t)
      (ordinaryLift s (t (cyclicPred s)) (t (cyclicSucc s)) t
        (nearFarInverse (coreNear s t) H0 boundaryUnitArray)) I = boundaryUnitArray I := by
  change nearFarTransform (tripleLift s (coreNear s t) t) (tripleLift s H0 t) _ I = _
  rw [nearFarTransform_spanning s I hI hL hR H0 (t (cyclicPred s)) (t (cyclicSucc s)) t t
      (nearFarInverse (coreNear s t) H0 boundaryUnitArray) hH ht,
    nearFarTransform_inverse, boundaryUnitArray_core_spanning_zero s I hI hL hR,
    boundaryUnitArray_spanning_zero s I hL hR, mul_zero]

end
end SM.SoftDuplication


#print axioms SM.SoftDuplication.spanning_zero_summand
#print axioms SM.SoftDuplication.spanning_one_summand
#print axioms SM.SoftDuplication.spanning_two_summand
#print axioms SM.SoftDuplication.spanning_cut_weighted_fiber_sum
#print axioms SM.SoftDuplication.spanning_weighted_fiber_sum
#print axioms SM.SoftDuplication.nearFarTransform_spanning
#print axioms SM.SoftDuplication.rootTransform_spanning
#print axioms SM.SoftDuplication.boundaryUnitArray_spanning_zero
#print axioms SM.SoftDuplication.boundaryUnitArray_core_spanning_zero
#print axioms SM.SoftDuplication.ordinaryLift_equation_spanning
