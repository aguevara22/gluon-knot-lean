import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InteriorCutSet
import Mathlib.Data.Subtype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

import Mathlib.Algebra.BigOperators.Fin

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

#print axioms SM.SoftDuplication.cutSubsetPair_cases
#print axioms SM.SoftDuplication.cutFiberCondition_empty
#print axioms SM.SoftDuplication.cutFiberCondition_spanning
#print axioms SM.SoftDuplication.cutFiberCondition_spanning_cut
#print axioms SM.SoftDuplication.cutFiberCondition_start
#print axioms SM.SoftDuplication.cutFiberCondition_end
#print axioms SM.SoftDuplication.emptyCutFiber
#print axioms SM.SoftDuplication.emptyCutFiberEquiv
#print axioms SM.SoftDuplication.spanningRows
#print axioms SM.SoftDuplication.spanningRowsEquiv
#print axioms SM.SoftDuplication.startingRows
#print axioms SM.SoftDuplication.startingRowsEquiv
#print axioms SM.SoftDuplication.endingRows
#print axioms SM.SoftDuplication.endingRowsEquiv
#print axioms SM.SoftDuplication.sum_emptyCutFiber
#print axioms SM.SoftDuplication.sum_spanningRows
#print axioms SM.SoftDuplication.sum_startingRows
#print axioms SM.SoftDuplication.sum_endingRows
