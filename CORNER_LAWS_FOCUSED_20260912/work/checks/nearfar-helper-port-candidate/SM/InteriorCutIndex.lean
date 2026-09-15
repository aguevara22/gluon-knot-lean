import SM.InteriorCutSet

namespace SM.IntervalComposition

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- The k-th strictly interior cut, retaining the actual boundary position. -/
def interiorPosition (π : IntervalComposition I) (k : Fin (π.parts - 1)) : Fin n :=
  π.cut ⟨k.val + 1, by have := k.isLt; omega⟩

theorem interiorPosition_injective (π : IntervalComposition I) :
    Function.Injective π.interiorPosition := by
  intro k l h
  have he := π.strict.injective h
  have hv := congrArg Fin.val he
  apply Fin.ext
  change k.val + 1 = l.val + 1 at hv
  omega

theorem interiorPosition_mem (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    π.interiorPosition k ∈ π.cutSet.interior.val := by
  have hl : I.left < π.interiorPosition k := by
    rw [← π.first]
    apply π.strict
    change 0 < k.val + 1
    omega
  have hr : π.interiorPosition k < I.right := by
    rw [← π.last]
    apply π.strict
    change k.val + 1 < π.parts
    have := k.isLt
    omega
  simp only [BoundaryCutSet.interior, Finset.mem_erase]
  refine ⟨ne_of_lt hr, ne_of_gt hl, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨k.val + 1, by have := k.isLt; omega⟩, Finset.mem_univ _, rfl⟩

/-- Every physical interior cut occurs at one of the interior cut indices. -/
theorem mem_interior_iff_exists_index (π : IntervalComposition I) (x : Fin n) :
    x ∈ π.cutSet.interior.val ↔ ∃ k : Fin (π.parts - 1), π.interiorPosition k = x := by
  constructor
  · intro hx
    have hbounds := π.cutSet.interior.property x hx
    simp only [BoundaryCutSet.interior, Finset.mem_erase] at hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx.2.2
    have hj0 : 0 < j.val := by
      by_contra h
      have he : j = 0 := by apply Fin.ext; change j.val = 0; omega
      have hpos := hbounds.1
      rw [← hj, he, π.first] at hpos
      exact (lt_irrefl _ hpos)
    have hjp : j.val < π.parts := by
      have hlt := j.isLt
      by_contra h
      have he : j = Fin.last π.parts := by
        apply Fin.ext
        change j.val = π.parts
        omega
      have hpos := hbounds.2
      rw [← hj, he, π.last] at hpos
      exact (lt_irrefl _ hpos)
    let k : Fin (π.parts - 1) := ⟨j.val - 1, by omega⟩
    refine ⟨k, ?_⟩
    have he : (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (π.parts + 1)) = j := by
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    change π.cut _ = x
    rw [he, hj]
  · rintro ⟨k, rfl⟩
    exact π.interiorPosition_mem k

/-- Exact index/physical-position equivalence, including the empty domain
when the composition is unary. -/
def interiorPositionEquiv (π : IntervalComposition I) :
    Fin (π.parts - 1) ≃ {x : Fin n // x ∈ π.cutSet.interior.val} :=
  Equiv.ofBijective (fun k => ⟨π.interiorPosition k, π.interiorPosition_mem k⟩) ⟨by
    intro k l he
    exact π.interiorPosition_injective (congrArg Subtype.val he), by
    intro x
    obtain ⟨k, hk⟩ := (π.mem_interior_iff_exists_index x.val).mp x.property
    exact ⟨k, Subtype.ext hk⟩⟩

end
end SM.IntervalComposition
