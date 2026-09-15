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
