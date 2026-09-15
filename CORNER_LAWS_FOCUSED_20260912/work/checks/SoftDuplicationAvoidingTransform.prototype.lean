import SM.RootBoundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import SM.InteriorCutSet
import Mathlib.Data.Subtype
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import SM.NearFar
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

#print axioms SM.SoftDuplication.nearFarWeight_avoiding
#print axioms SM.SoftDuplication.ordinaryLift_child_avoiding
#print axioms SM.SoftDuplication.ordinaryLift_children_avoiding
#print axioms SM.SoftDuplication.nearFarTransform_ordinaryLift_avoiding
#print axioms SM.SoftDuplication.ordinaryLift_equation_avoiding
#print axioms SM.SoftDuplication.tripleLift_neg
#print axioms SM.SoftDuplication.rootTransform_ordinaryLift_avoiding
