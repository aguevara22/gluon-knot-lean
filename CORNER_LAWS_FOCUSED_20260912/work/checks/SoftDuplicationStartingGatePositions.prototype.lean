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

#print axioms SM.SoftDuplication.starting_mem_interior_iff
#print axioms SM.SoftDuplication.starting_old_endpoints
#print axioms SM.SoftDuplication.starting_interior_gt
#print axioms SM.SoftDuplication.starting_zero_interior
#print axioms SM.SoftDuplication.starting_one_interior
#print axioms SM.SoftDuplication.startingInteriorZeroMap
#print axioms SM.SoftDuplication.startingInteriorZeroEquiv
#print axioms SM.SoftDuplication.startingInteriorZeroEquiv_val
#print axioms SM.SoftDuplication.startingInteriorOneMap
#print axioms SM.SoftDuplication.startingInteriorOneEquiv
#print axioms SM.SoftDuplication.startingInteriorOneEquiv_inl_val
#print axioms SM.SoftDuplication.startingInteriorOneEquiv_inr_val
#print axioms SM.SoftDuplication.starting_zero_nearTriple
#print axioms SM.SoftDuplication.starting_zero_farTriple
#print axioms SM.SoftDuplication.starting_one_nearTriple
#print axioms SM.SoftDuplication.starting_one_farTriple
#print axioms SM.SoftDuplication.starting_new_near_positions
#print axioms SM.SoftDuplication.starting_new_far_positions
