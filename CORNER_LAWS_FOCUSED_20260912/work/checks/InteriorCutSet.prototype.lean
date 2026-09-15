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

#print axioms SM.BoundaryCutSet.interior_ofInterior
#print axioms SM.BoundaryCutSet.ofInterior_interior
#print axioms SM.BoundaryCutSet.interiorEquiv
#print axioms SM.BoundaryCutSet.mem_restrict
#print axioms SM.BoundaryCutSet.restrict_self
#print axioms SM.BoundaryCutSet.restrict_restrict
#print axioms SM.IntervalComposition.interiorCutSetEquiv
