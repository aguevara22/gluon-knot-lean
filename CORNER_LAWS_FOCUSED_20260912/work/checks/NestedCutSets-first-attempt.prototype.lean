import SM.FiniteCompositions
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The complete cut set of a composition, including both endpoints.
No interior position is required or forbidden. -/
structure BoundaryCutSet (I : BoundaryInterval n) where
  cuts : Finset (Fin n)
  left_mem : I.left ∈ cuts
  right_mem : I.right ∈ cuts
  bounds : ∀ x ∈ cuts, I.left ≤ x ∧ x ≤ I.right

namespace BoundaryCutSet
variable {I : BoundaryInterval n}

@[ext] theorem ext (S T : BoundaryCutSet I) (h : S.cuts = T.cuts) : S = T := by
  cases S
  cases T
  cases h
  rfl

theorem card_ge_two (S : BoundaryCutSet I) : 2 ≤ S.cuts.card := by
  have h : ({I.left, I.right} : Finset (Fin n)) ⊆ S.cuts := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact S.left_mem
    · exact S.right_mem
  have hc := Finset.card_le_card h
  simpa [ne_of_lt I.increasing] using hc

/-- Sorting all cuts recovers a raw source composition. The part count is
one fewer than the number of cuts, not an independently chosen bound. -/
def toComposition (S : BoundaryCutSet I) : IntervalComposition I where
  parts := S.cuts.card - 1
  parts_pos := by have := S.card_ge_two; omega
  cut := S.cuts.orderEmbOfFin (by have := S.card_ge_two; omega)
  strict := (S.cuts.orderEmbOfFin (by have := S.card_ge_two; omega)).strictMono
  first := by
    let h : S.cuts.card = S.cuts.card - 1 + 1 := by have := S.card_ge_two; omega
    let e := S.cuts.orderIsoOfFin h
    let k := e.symm ⟨I.left, S.left_mem⟩
    have hk : S.cuts.orderEmbOfFin h k = I.left :=
      congrArg Subtype.val (e.apply_symm_apply ⟨I.left, S.left_mem⟩)
    apply le_antisymm
    · calc
        S.cuts.orderEmbOfFin h 0 ≤ S.cuts.orderEmbOfFin h k :=
          (S.cuts.orderEmbOfFin h).monotone (Fin.zero_le _)
        _ = I.left := hk
    · exact (S.bounds _ (Finset.orderEmbOfFin_mem _ h _)).1
  last := by
    let h : S.cuts.card = S.cuts.card - 1 + 1 := by have := S.card_ge_two; omega
    let e := S.cuts.orderIsoOfFin h
    let k := e.symm ⟨I.right, S.right_mem⟩
    have hk : S.cuts.orderEmbOfFin h k = I.right :=
      congrArg Subtype.val (e.apply_symm_apply ⟨I.right, S.right_mem⟩)
    apply le_antisymm
    · exact (S.bounds _ (Finset.orderEmbOfFin_mem _ h _)).2
    · calc
        I.right = S.cuts.orderEmbOfFin h k := hk.symm
        _ ≤ S.cuts.orderEmbOfFin h (Fin.last (S.cuts.card - 1)) :=
          (S.cuts.orderEmbOfFin h).monotone (Fin.le_last _)

end BoundaryCutSet

namespace IntervalComposition
variable {I : BoundaryInterval n}

/-- The full ordered composition is retained as its finite set of cuts. -/
def cutSet (π : IntervalComposition I) : BoundaryCutSet I where
  cuts := Finset.univ.image π.cut
  left_mem := by rw [← π.first]; exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  right_mem := by
    rw [← π.last]
    exact Finset.mem_image.mpr ⟨Fin.last π.parts, Finset.mem_univ _, rfl⟩
  bounds := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    constructor
    · rw [← π.first]; exact π.strict.monotone (Fin.zero_le _)
    · rw [← π.last]; exact π.strict.monotone (Fin.le_last _)

theorem cutSet_card (π : IntervalComposition I) : π.cutSet.cuts.card = π.parts + 1 := by
  simp [cutSet, Finset.card_image_of_injective, π.strict.injective]

theorem cutSet_injective : Function.Injective (cutSet (I := I)) := by
  intro π ρ he
  have hset := congrArg BoundaryCutSet.cuts he
  have hp : π.parts = ρ.parts := by
    have := congrArg Finset.card hset
    rw [cutSet_card, cutSet_card] at this
    omega
  cases π with
  | mk p hp0 c hc cf cl =>
    cases ρ with
    | mk q hq0 d hd df dl =>
      change p = q at hp
      subst q
      have hcd : c = d := by
        have hc' : c = (Finset.univ.image c).orderEmbOfFin
            (show (Finset.univ.image c).card = p + 1 by
              simp [Finset.card_image_of_injective, hc.injective]) :=
          Finset.orderEmbOfFin_unique _
            (fun k => Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) hc
        have hd' : d = (Finset.univ.image c).orderEmbOfFin
            (show (Finset.univ.image c).card = p + 1 by
              simp [Finset.card_image_of_injective, hc.injective]) := by
          apply Finset.orderEmbOfFin_unique
          · intro k
            change Finset.univ.image c = Finset.univ.image d at hset
            rw [hset]
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
          · exact hd
        exact hc'.trans hd'.symm
      subst d
      rfl

end IntervalComposition

namespace BoundaryCutSet
variable {I : BoundaryInterval n}

theorem toComposition_cutSet (S : BoundaryCutSet I) : S.toComposition.cutSet = S := by
  apply BoundaryCutSet.ext
  exact Finset.image_orderEmbOfFin_univ _ _

end BoundaryCutSet

namespace IntervalComposition
variable {I : BoundaryInterval n}

theorem cutSet_toComposition (π : IntervalComposition I) : π.cutSet.toComposition = π := by
  apply cutSet_injective
  exact BoundaryCutSet.toComposition_cutSet π.cutSet

/-- Every raw strictly increasing composition corresponds to exactly one set
of boundary cuts, including the unary set consisting of the two endpoints. -/
def cutSetEquiv (I : BoundaryInterval n) : IntervalComposition I ≃ BoundaryCutSet I where
  toFun := cutSet
  invFun := BoundaryCutSet.toComposition
  left_inv := cutSet_toComposition
  right_inv := BoundaryCutSet.toComposition_cutSet

end IntervalComposition

end
end SM

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- An arbitrary finite selection of strictly interior positions. -/
abbrev InteriorCutSet (I : BoundaryInterval n) :=
  {s : Finset (Fin n) // ∀ x ∈ s, I.left < x ∧ x < I.right}

namespace BoundaryCutSet
variable {I : BoundaryInterval n}

/-- Remove exactly the two endpoint cuts. -/
def interior (S : BoundaryCutSet I) : InteriorCutSet I :=
  ⟨(S.cuts.erase I.left).erase I.right, by
    intro x hx
    simp only [Finset.mem_erase] at hx
    have hb := S.bounds x hx.2.2
    exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hx.2.1), lt_of_le_of_ne hb.2 hx.1⟩⟩

/-- Adjoin exactly the interval endpoints to any interior selection. -/
def ofInterior (s : InteriorCutSet I) : BoundaryCutSet I where
  cuts := insert I.left (insert I.right s.val)
  left_mem := Finset.mem_insert_self _ _
  right_mem := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  bounds := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, le_of_lt I.increasing⟩
    · exact ⟨le_of_lt I.increasing, le_rfl⟩
    · exact ⟨le_of_lt (s.property x hx).1, le_of_lt (s.property x hx).2⟩

theorem interior_ofInterior (s : InteriorCutSet I) : (ofInterior s).interior = s := by
  apply Subtype.ext
  ext x
  simp only [interior, ofInterior, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨hr, hl, hx | hx | hx⟩
    · exact False.elim (hl hx)
    · exact False.elim (hr hx)
    · exact hx
  · intro hx
    have h := s.property x hx
    exact ⟨ne_of_lt h.2, ne_of_gt h.1, Or.inr (Or.inr hx)⟩

theorem ofInterior_interior (S : BoundaryCutSet I) : ofInterior S.interior = S := by
  apply BoundaryCutSet.ext
  ext x
  simp only [ofInterior, interior, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl | ⟨_, _, hx⟩)
    · exact S.left_mem
    · exact S.right_mem
    · exact hx
  · intro hx
    by_cases hl : x = I.left
    · exact Or.inl hl
    · by_cases hr : x = I.right
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr ⟨hr, hl, hx⟩)

/-- Endpoints are fixed; every subset of interior positions is allowed. -/
def interiorEquiv (I : BoundaryInterval n) : BoundaryCutSet I ≃ InteriorCutSet I where
  toFun := interior
  invFun := ofInterior
  left_inv := ofInterior_interior
  right_inv := interior_ofInterior

/-- Restrict the actual cut positions to any interval whose endpoints occur
among them. No endpoint or interior cut inside the interval is lost. -/
def restrict (S : BoundaryCutSet I) (J : BoundaryInterval n)
    (hl : J.left ∈ S.cuts) (hr : J.right ∈ S.cuts) : BoundaryCutSet J where
  cuts := S.cuts.filter (fun x => J.left ≤ x ∧ x ≤ J.right)
  left_mem := Finset.mem_filter.mpr ⟨hl, le_rfl, le_of_lt J.increasing⟩
  right_mem := Finset.mem_filter.mpr ⟨hr, le_of_lt J.increasing, le_rfl⟩
  bounds := by intro x hx; exact (Finset.mem_filter.mp hx).2

theorem mem_restrict (S : BoundaryCutSet I) (J : BoundaryInterval n)
    (hl : J.left ∈ S.cuts) (hr : J.right ∈ S.cuts) (x : Fin n) :
    x ∈ (S.restrict J hl hr).cuts ↔ x ∈ S.cuts ∧ J.left ≤ x ∧ x ≤ J.right :=
  Finset.mem_filter

theorem restrict_self (S : BoundaryCutSet I) :
    S.restrict I S.left_mem S.right_mem = S := by
  apply BoundaryCutSet.ext
  ext x
  simp only [mem_restrict]
  exact ⟨fun h => h.1, fun h => ⟨h, S.bounds x h⟩⟩

theorem restrict_restrict (S : BoundaryCutSet I) (J K : BoundaryInterval n)
    (hjl : J.left ∈ S.cuts) (hjr : J.right ∈ S.cuts)
    (hkl : K.left ∈ (S.restrict J hjl hjr).cuts)
    (hkr : K.right ∈ (S.restrict J hjl hjr).cuts) :
    (S.restrict J hjl hjr).restrict K hkl hkr =
      S.restrict K (Finset.mem_filter.mp hkl).1 (Finset.mem_filter.mp hkr).1 := by
  apply BoundaryCutSet.ext
  ext x
  simp only [mem_restrict]
  constructor
  · rintro ⟨⟨hx, _, _⟩, hxl, hxr⟩
    exact ⟨hx, hxl, hxr⟩
  · rintro ⟨hx, hxl, hxr⟩
    have hleft := (Finset.mem_filter.mp hkl).2.1
    have hright := (Finset.mem_filter.mp hkr).2.2
    exact ⟨⟨hx, le_trans hleft hxl, le_trans hxr hright⟩, hxl, hxr⟩

end BoundaryCutSet

namespace IntervalComposition

/-- The source composition domain is exactly all subsets of its interior
boundary positions, with the empty subset retaining the unary term. -/
def interiorCutSetEquiv (I : BoundaryInterval n) : IntervalComposition I ≃ InteriorCutSet I :=
  (cutSetEquiv I).trans (BoundaryCutSet.interiorEquiv I)

end IntervalComposition

end
end SM

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Every part lies in the original interval. -/
theorem part_bounds (π : IntervalComposition I) (k : Fin π.parts) :
    I.left ≤ (π.part k).left ∧ (π.part k).right ≤ I.right := by
  constructor
  · rw [← π.first]
    exact π.strict.monotone (Fin.zero_le k.castSucc)
  · rw [← π.last]
    exact π.strict.monotone (Fin.le_last k.succ)

/-- Earlier parts end no later than later parts begin. -/
theorem part_order (π : IntervalComposition I) {k l : Fin π.parts} (h : k < l) :
    (π.part k).right ≤ (π.part l).left := by
  apply π.strict.monotone
  change k.val + 1 ≤ l.val
  exact h

/-- Every point before the final endpoint belongs to a unique half-open part;
the proof chooses the largest cut whose position does not exceed that point. -/
theorem exists_halfOpen_part (π : IntervalComposition I) (x : Fin n)
    (hl : I.left ≤ x) (hr : x < I.right) :
    ∃ k : Fin π.parts, (π.part k).left ≤ x ∧ x < (π.part k).right := by
  classical
  let s := Finset.univ.filter (fun j : Fin (π.parts + 1) => π.cut j ≤ x)
  have hs : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [π.first] using hl⟩⟩
  let j := s.max' hs
  have hj : π.cut j ≤ x := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hjp : j.val < π.parts := by
    have hn : j ≠ Fin.last π.parts := by
      intro he
      rw [he, π.last] at hj
      exact (not_le_of_gt hr) hj
    have hjb := j.isLt
    have hne : j.val ≠ π.parts := by
      intro he
      exact hn (Fin.ext (by simpa using he))
    omega
  let k : Fin π.parts := ⟨j.val, hjp⟩
  have hk : k.castSucc = j := by apply Fin.ext; rfl
  refine ⟨k, ?_, ?_⟩
  · change π.cut k.castSucc ≤ x
    rw [hk]
    exact hj
  · change x < π.cut k.succ
    by_contra h
    have he : k.succ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩
    have hh : k.succ ≤ j := Finset.le_max' s _ he
    change j.val + 1 ≤ j.val at hh
    omega

/-- Closed parts cover both interval endpoints as well as its interior. -/
theorem exists_closed_part (π : IntervalComposition I) (x : Fin n)
    (hl : I.left ≤ x) (hr : x ≤ I.right) :
    ∃ k : Fin π.parts, (π.part k).left ≤ x ∧ x ≤ (π.part k).right := by
  by_cases he : x = I.right
  · let k : Fin π.parts := ⟨π.parts - 1, by have := π.parts_pos; omega⟩
    have hk : k.succ = Fin.last π.parts := by
      apply Fin.ext
      change π.parts - 1 + 1 = π.parts
      have := π.parts_pos
      omega
    have hright : (π.part k).right = I.right := by
      change π.cut k.succ = I.right
      rw [hk, π.last]
    exact ⟨k, by rw [he, ← hright]; exact le_of_lt (π.part k).increasing,
      by rw [he, hright]⟩
  · obtain ⟨k, hk⟩ := π.exists_halfOpen_part x hl (lt_of_le_of_ne hr he)
    exact ⟨k, hk.1, le_of_lt hk.2⟩

/-- Distinct part interiors cannot overlap. Shared endpoints are allowed. -/
theorem part_interior_unique (π : IntervalComposition I) (x : Fin n)
    {k l : Fin π.parts} (hk : (π.part k).left < x ∧ x < (π.part k).right)
    (hl : (π.part l).left < x ∧ x < (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · have hle := π.part_order h
    exact False.elim ((not_lt_of_ge hle) (lt_trans hl.1 hk.2))
  · exact h
  · have hle := π.part_order h
    exact False.elim ((not_lt_of_ge hle) (lt_trans hk.1 hl.2))

end
end SM.IntervalComposition

namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- A refined cut set contains all cuts of the chosen outer composition. -/
abbrev RefiningCutSet (π : IntervalComposition I) :=
  {S : BoundaryCutSet I // π.cutSet.cuts ⊆ S.cuts}

namespace IntervalComposition

/-- Half-open part membership is unique, including points at a shared cut. -/
theorem halfOpen_part_unique (π : IntervalComposition I) (x : Fin n)
    {k l : Fin π.parts} (hk : (π.part k).left ≤ x ∧ x < (π.part k).right)
    (hl : (π.part l).left ≤ x ∧ x < (π.part l).right) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim ((not_le_of_gt hk.2) (le_trans (π.part_order h) hl.1))
  · exact h
  · exact False.elim ((not_le_of_gt hl.2) (le_trans (π.part_order h) hk.1))

/-- The ordered union of every inner composition's cuts. Common endpoints
are identified as the same boundary position. -/
def flattenCutSets (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) : BoundaryCutSet I where
  cuts := Finset.univ.biUnion (fun k => (S k).cuts)
  left_mem := by
    let k : Fin π.parts := ⟨0, π.parts_pos⟩
    have hk : (π.part k).left = I.left := π.first
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_univ _, hk ▸ (S k).left_mem⟩
  right_mem := by
    let k : Fin π.parts := ⟨π.parts - 1, by have := π.parts_pos; omega⟩
    have hs : k.succ = Fin.last π.parts := by
      apply Fin.ext
      change π.parts - 1 + 1 = π.parts
      have := π.parts_pos
      omega
    have hk : (π.part k).right = I.right := by change π.cut k.succ = I.right; rw [hs, π.last]
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hk ▸ (S k).right_mem⟩
  bounds := by
    intro x hx
    obtain ⟨k, _, hx⟩ := Finset.mem_biUnion.mp hx
    have hs := (S k).bounds x hx
    have hp := π.part_bounds k
    exact ⟨le_trans hp.1 hs.1, le_trans hs.2 hp.2⟩

theorem mem_flattenCutSets (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) (x : Fin n) :
    x ∈ (π.flattenCutSets S).cuts ↔ ∃ k, x ∈ (S k).cuts := by
  simp [flattenCutSets]

/-- Every outer cut remains in the union, including both global endpoints. -/
theorem outer_cuts_subset_flatten (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) :
    π.cutSet.cuts ⊆ (π.flattenCutSets S).cuts := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_flattenCutSets]
  by_cases hj : j.val < π.parts
  · let k : Fin π.parts := ⟨j.val, hj⟩
    have hk : k.castSucc = j := by apply Fin.ext; rfl
    refine ⟨k, ?_⟩
    have he : (π.part k).left = π.cut j := by change π.cut k.castSucc = π.cut j; rw [hk]
    exact he ▸ (S k).left_mem
  · have he : j = Fin.last π.parts := by
      apply Fin.ext
      have := j.isLt
      change j.val = π.parts
      omega
    rw [he, π.last]
    exact (mem_flattenCutSets π S I.right).mp (π.flattenCutSets S).right_mem

def flattenRefinement (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) : RefiningCutSet π :=
  ⟨π.flattenCutSets S, π.outer_cuts_subset_flatten S⟩

/-- Recover each inner composition's exact cut set by interval restriction. -/
def unflattenCutSets (π : IntervalComposition I) (T : RefiningCutSet π)
    (k : Fin π.parts) : BoundaryCutSet (π.part k) :=
  T.val.restrict (π.part k)
    (T.property (Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩))
    (T.property (Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩))

/-- Restricting a union to an outer part recovers its inner cut set.
Cuts coming from different parts can enter only at a shared endpoint. -/
theorem unflatten_flatten (π : IntervalComposition I)
    (S : ∀ k : Fin π.parts, BoundaryCutSet (π.part k)) :
    π.unflattenCutSets (π.flattenRefinement S) = S := by
  funext k
  apply BoundaryCutSet.ext
  ext x
  simp only [unflattenCutSets, BoundaryCutSet.mem_restrict, flattenRefinement]
  constructor
  · rintro ⟨hx, hkl, hkr⟩
    obtain ⟨l, hl⟩ := (π.mem_flattenCutSets S x).mp hx
    rcases lt_trichotomy l k with h | h | h
    · have hb := (S l).bounds x hl
      have ho := π.part_order h
      have he : x = (π.part k).left := le_antisymm (le_trans hb.2 ho) hkl
      rw [he]
      exact (S k).left_mem
    · simpa [h] using hl
    · have hb := (S l).bounds x hl
      have ho := π.part_order h
      have he : x = (π.part k).right := le_antisymm hkr (le_trans ho hb.1)
      rw [he]
      exact (S k).right_mem
  · intro hx
    exact ⟨(π.mem_flattenCutSets S x).mpr ⟨k, hx⟩, (S k).bounds x hx⟩

/-- Every refined cut is covered by some outer part, so union after
restriction retains the entire refined cut set. -/
theorem flatten_unflatten (π : IntervalComposition I) (T : RefiningCutSet π) :
    π.flattenRefinement (π.unflattenCutSets T) = T := by
  apply Subtype.ext
  apply BoundaryCutSet.ext
  ext x
  change x ∈ (π.flattenCutSets (π.unflattenCutSets T)).cuts ↔ x ∈ T.val.cuts
  rw [mem_flattenCutSets]
  constructor
  · rintro ⟨k, hk⟩
    exact (Finset.mem_filter.mp hk).1
  · intro hx
    have hb := T.val.bounds x hx
    obtain ⟨k, hk⟩ := π.exists_closed_part x hb.1 hb.2
    exact ⟨k, Finset.mem_filter.mpr ⟨hx, hk⟩⟩

/-- The actual nested cut data and refined cut sets are inverse descriptions
for every outer composition, including the unary outer composition. -/
def nestedCutSetEquiv (π : IntervalComposition I) :
    (∀ k : Fin π.parts, BoundaryCutSet (π.part k)) ≃ RefiningCutSet π where
  toFun := π.flattenRefinement
  invFun := π.unflattenCutSets
  left_inv := π.unflatten_flatten
  right_inv := π.flatten_unflatten

/-- Every family of raw inner compositions corresponds bijectively to a
refining cut set. No inner arity or endpoint case has been excluded. -/
def nestedCompositionEquiv (π : IntervalComposition I) :
    (∀ k : Fin π.parts, IntervalComposition (π.part k)) ≃ RefiningCutSet π :=
  (Equiv.piCongrRight (fun k => cutSetEquiv (π.part k))).trans π.nestedCutSetEquiv

end IntervalComposition

end
end SM

#print axioms SM.IntervalComposition.halfOpen_part_unique
#print axioms SM.IntervalComposition.mem_flattenCutSets
#print axioms SM.IntervalComposition.outer_cuts_subset_flatten
#print axioms SM.IntervalComposition.unflatten_flatten
#print axioms SM.IntervalComposition.flatten_unflatten
#print axioms SM.IntervalComposition.nestedCutSetEquiv
#print axioms SM.IntervalComposition.nestedCompositionEquiv
