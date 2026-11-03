import DirectGLSSW.BooleanInversion
import DirectGLSSW.CutIncidence

/-!
# Gate expansion by selected outer cuts

Source: `ep:factorization`. Finite distributivity is reindexed by the actual
middle vertices of cut triples; no neighbor or weight identification is assumed.
-/

namespace DirectGLSSW
open scoped BigOperators

/-- Expand a product after labeling its factors injectively. The complement
product retains the original factors, rather than choosing representatives. -/
theorem prod_add_by_label {α β R : Type*} [DecidableEq α] [DecidableEq β]
    [CommSemiring R] (s : Finset α) (label : α → β)
    (hinj : Set.InjOn label (s : Set α)) (f : β → R) (g : α → R) :
    (∏ x ∈ s, (f (label x) + g x)) =
      ∑ u ∈ (s.image label).powerset,
        (∏ a ∈ u, f a) * ∏ x ∈ s.filter (fun x => label x ∉ u), g x := by
  classical
  rw [Finset.prod_add]
  refine Finset.sum_bij'
    (fun t _ => t.image label)
    (fun u _ => s.filter (fun x => label x ∈ u)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_powerset.mpr (Finset.image_subset_image (Finset.mem_powerset.mp ht))
  · intro u _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, y, hy, heq⟩
      have hxy : y = x := hinj (hts hy) hx heq
      simpa [hxy] using hy
    · intro hx
      exact ⟨hts hx, x, hx, rfl⟩
  · intro u hu
    have hus := Finset.mem_powerset.mp hu
    ext a
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hus ha)
      exact ⟨x, ⟨hx, ha⟩, rfl⟩
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    have hp : (∏ a ∈ t.image label, f a) = ∏ x ∈ t, f (label x) :=
      Finset.prod_image (fun x hx y hy heq => hinj (hts hx) (hts hy) heq)
    have hc : s.filter (fun x => label x ∉ t.image label) = s \ t := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hx, hn⟩
        exact ⟨hx, fun hxt => hn (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)⟩
      · rintro ⟨hx, hn⟩
        refine ⟨hx, ?_⟩
        rintro ha
        obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ha
        exact hn ((hinj (hts hy) hx heq) ▸ hy)
    rw [hp, hc]

/-- With zero near data, only each cut's middle vertex enters its gate. -/
theorem gateProduct_zero_near (H : TripleArray) {i j : ℕ} {S : Finset ℕ}
    (hij : i < j) (hS : S ⊆ Finset.Ioo i j) :
    gateProduct (fun _ _ _ => 0) H i j (cutVertices i j S) =
      ∏ k ∈ S, -H i k j / 2 := by
  rw [gateProduct_eq_prod_cutTriples _ _ hij hS]
  simp only [zero_sub]
  calc
    _ = ∏ k ∈ (cutTriples i j S).image (fun t => t.2.1), -H i k j / 2 :=
      (Finset.prod_image (f := fun k => -H i k j / 2) (fun t ht u hu htu =>
        cutTriples_middle_injective hij hS ht hu htu)).symm
    _ = _ := by rw [cutTriples_middle_image hij hS]

/-- A final cut list with a selected outer subset: outer cuts carry far
weights, remaining triples carry their actual final-neighbor near weights. -/
def cutRefinementWeight (D H : TripleArray) (X : IntervalArray)
    (i j : ℕ) (T S : Finset ℕ) : ℚ :=
  (∏ k ∈ S, -H i k j / 2) *
    (∏ t ∈ (cutTriples i j T).filter (fun t => t.2.1 ∉ S), D t.1 t.2.1 t.2.2 / 2) *
    branchProduct X (cutVertices i j T)

/-- Distribute every actual gate into its far and near contributions, and
index the resulting terms by precisely the selected outer cut vertices. -/
theorem cutContribution_eq_sum_refinementWeights (D H : TripleArray) (X : IntervalArray)
    {i j : ℕ} {T : Finset ℕ} (hij : i < j) (hT : T ⊆ Finset.Ioo i j) :
    cutContribution D H X i j T =
      ∑ S ∈ T.powerset, cutRefinementWeight D H X i j T S := by
  unfold cutContribution
  rw [gateProduct_eq_prod_cutTriples _ _ hij hT]
  have hsplit :
      (∏ t ∈ cutTriples i j T, (D t.1 t.2.1 t.2.2 - H i t.2.1 j) / 2) =
      ∏ t ∈ cutTriples i j T, (-H i t.2.1 j / 2 + D t.1 t.2.1 t.2.2 / 2) := by
    apply Finset.prod_congr rfl
    intro t _
    ring
  rw [hsplit, prod_add_by_label (cutTriples i j T) (fun t => t.2.1)
    (fun t ht u hu htu => cutTriples_middle_injective hij hT ht hu htu)
    (fun k => -H i k j / 2) (fun t => D t.1 t.2.1 t.2.2 / 2),
    cutTriples_middle_image hij hT, Finset.sum_mul]
  rfl

end DirectGLSSW
