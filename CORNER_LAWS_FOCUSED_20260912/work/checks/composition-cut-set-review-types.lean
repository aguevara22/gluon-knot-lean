import SM.FiniteCompositions
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic
set_option pp.fullNames true
set_option pp.universes false
namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

namespace IntervalComposition
variable {I : BoundaryInterval n}

/-- A one-part composition has only its two fixed endpoints. -/
theorem eq_single_of_parts_eq_one (π : IntervalComposition I) (hparts : π.parts = 1) :
    π = single I := by
  cases π with
  | mk parts hp cut hstrict hfirst hlast =>
    change parts = 1 at hparts
    subst parts
    have hc : cut = ![I.left, I.right] := by
      funext k
      fin_cases k
      · exact hfirst
      · exact hlast
    subst cut
    rfl

theorem parts_eq_one_iff_eq_single (π : IntervalComposition I) :
    π.parts = 1 ↔ π = single I :=
  ⟨π.eq_single_of_parts_eq_one, fun h => by rw [h]; rfl⟩

/-- The sole part of the unary composition is exactly the original interval. -/
theorem single_part (I : BoundaryInterval n) (k : Fin (single I).parts) :
    (single I).part k = I := by
  change Fin 1 at k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  rfl

theorem single_product {R : Type*} [CommMonoid R]
    (X : BoundaryInterval n → R) (I : BoundaryInterval n) :
    (∏ k : Fin (single I).parts, X ((single I).part k)) = X I := by
  simp only [single_part]
  exact Fin.prod_univ_one (fun _ => X I)

/-- Every nonunary composition has at least two parts; its underlying cuts
are unchanged by this equivalence. -/
def nonSingleEquiv (I : BoundaryInterval n) :
    {π : IntervalComposition I // π ≠ single I} ≃
      {π : IntervalComposition I // 2 ≤ π.parts} :=
  Equiv.subtypeEquivRight (fun π => by
    constructor
    · intro h
      have hn : π.parts ≠ 1 := fun hp => h (π.eq_single_of_parts_eq_one hp)
      have := π.parts_pos
      omega
    · intro h he
      have hp : π.parts = 1 := π.parts_eq_one_iff_eq_single.mpr he
      omega)

end IntervalComposition

end

end SM

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

#check SM.IntervalComposition.eq_single_of_parts_eq_one
#print axioms SM.IntervalComposition.eq_single_of_parts_eq_one
#check SM.IntervalComposition.parts_eq_one_iff_eq_single
#print axioms SM.IntervalComposition.parts_eq_one_iff_eq_single
#check SM.IntervalComposition.single_part
#print axioms SM.IntervalComposition.single_part
#check SM.IntervalComposition.single_product
#print axioms SM.IntervalComposition.single_product
#check SM.IntervalComposition.nonSingleEquiv
#print axioms SM.IntervalComposition.nonSingleEquiv
#check SM.BoundaryCutSet
#print axioms SM.BoundaryCutSet
#check SM.BoundaryCutSet.ext
#print axioms SM.BoundaryCutSet.ext
#check SM.BoundaryCutSet.card_ge_two
#print axioms SM.BoundaryCutSet.card_ge_two
#check SM.BoundaryCutSet.toComposition
#print axioms SM.BoundaryCutSet.toComposition
#check SM.IntervalComposition.cutSet
#print axioms SM.IntervalComposition.cutSet
#check SM.IntervalComposition.cutSet_card
#print axioms SM.IntervalComposition.cutSet_card
#check SM.IntervalComposition.cutSet_injective
#print axioms SM.IntervalComposition.cutSet_injective
#check SM.BoundaryCutSet.toComposition_cutSet
#print axioms SM.BoundaryCutSet.toComposition_cutSet
#check SM.IntervalComposition.cutSet_toComposition
#print axioms SM.IntervalComposition.cutSet_toComposition
#check SM.IntervalComposition.cutSetEquiv
#print axioms SM.IntervalComposition.cutSetEquiv
#print SM.BoundaryCutSet
#print SM.BoundaryCutSet.toComposition
#print SM.IntervalComposition.cutSet
namespace CompositionCutSetIndependentReview
open SM
variable {n : ℕ} [NeZero n]

def endpointSet (I : BoundaryInterval n) : BoundaryCutSet I where
  cuts := {I.left, I.right}
  left_mem := by simp
  right_mem := by simp
  bounds := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact ⟨by simp [I.increasing.le], by simp [I.increasing.le]⟩

def fullCutSet (I : BoundaryInterval n) : BoundaryCutSet I where
  cuts := Finset.Icc I.left I.right
  left_mem := Finset.mem_Icc.mpr ⟨le_rfl, I.increasing.le⟩
  right_mem := Finset.mem_Icc.mpr ⟨I.increasing.le, le_rfl⟩
  bounds := fun _ hx => Finset.mem_Icc.mp hx

-- No bounded endpoint-containing finite cut set is omitted.
theorem every_raw_cut_set_admitted (I : BoundaryInterval n) (C : Finset (Fin n))
    (hl : I.left ∈ C) (hr : I.right ∈ C)
    (hb : ∀ x ∈ C, I.left ≤ x ∧ x ≤ I.right) :
    ∃ π : IntervalComposition I, π.cutSet.cuts = C ∧ π.parts + 1 = C.card := by
  let S : BoundaryCutSet I := ⟨C, hl, hr, hb⟩
  refine ⟨S.toComposition, ?_, ?_⟩
  · exact congrArg BoundaryCutSet.cuts S.toComposition_cutSet
  · have hs := congrArg (fun T : BoundaryCutSet I => T.cuts.card) S.toComposition_cutSet
    rw [IntervalComposition.cutSet_card] at hs
    exact hs

theorem unary_cut_set_is_exactly_endpoints (I : BoundaryInterval n) :
    (IntervalComposition.single I).cutSet = endpointSet I ∧
      (endpointSet I).toComposition = IntervalComposition.single I := by
  have hp : (endpointSet I).toComposition.parts = 1 := by
    simp [BoundaryCutSet.toComposition, endpointSet, ne_of_lt I.increasing]
  have he := (endpointSet I).toComposition.eq_single_of_parts_eq_one hp
  refine ⟨?_, he⟩
  rw [← he]
  exact (endpointSet I).toComposition_cutSet

-- Full cuts are allowed, have maximal source arity, and retain every position.
theorem full_cut_coverage (I : BoundaryInterval n) :
    (fullCutSet I).toComposition.cutSet.cuts = Finset.Icc I.left I.right ∧
      (fullCutSet I).toComposition.parts = I.leaves := by
  constructor
  · exact congrArg BoundaryCutSet.cuts (fullCutSet I).toComposition_cutSet
  · simp only [BoundaryCutSet.toComposition, fullCutSet, Fin.card_Icc, BoundaryInterval.leaves]
    have := I.increasing
    change I.right.val + 1 - I.left.val - 1 = I.right.val - I.left.val
    omega

-- Sorted reconstruction has all and only the original cuts.
theorem exact_cut_membership (I : BoundaryInterval n) (S : BoundaryCutSet I) (x : Fin n) :
    (∃ k, S.toComposition.cut k = x) ↔ x ∈ S.cuts := by
  have hs := congrArg BoundaryCutSet.cuts S.toComposition_cutSet
  change Finset.univ.image S.toComposition.cut = S.cuts at hs
  rw [← hs]
  simp

-- Full raw composition data, including its natural part count and dependent
-- cut function, are recovered rather than only an equal cardinality.
theorem complete_raw_roundtrip (I : BoundaryInterval n) (π : IntervalComposition I) :
    π.cutSet.toComposition.parts = π.parts ∧ HEq π.cutSet.toComposition.cut π.cut := by
  rw [π.cutSet_toComposition]
  exact ⟨rfl, HEq.rfl⟩

theorem same_cut_set_iff_same_composition (I : BoundaryInterval n)
    (π ρ : IntervalComposition I) : π.cutSet.cuts = ρ.cutSet.cuts ↔ π = ρ := by
  constructor
  · intro h
    exact IntervalComposition.cutSet_injective (BoundaryCutSet.ext _ _ h)
  · rintro rfl
    rfl

end CompositionCutSetIndependentReview

#print axioms CompositionCutSetIndependentReview.every_raw_cut_set_admitted
#print axioms CompositionCutSetIndependentReview.unary_cut_set_is_exactly_endpoints
#print axioms CompositionCutSetIndependentReview.full_cut_coverage
#print axioms CompositionCutSetIndependentReview.exact_cut_membership
#print axioms CompositionCutSetIndependentReview.complete_raw_roundtrip
#print axioms CompositionCutSetIndependentReview.same_cut_set_iff_same_composition
