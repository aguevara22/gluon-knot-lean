import SM.TreeCoefficient
import SM.PlaneTreeWeights

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

def openPlaneTreeSum (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) : R := ∑ T : OpenPlaneTree I, T.weight ordinary

theorem OpenPlaneTree.eq_leaf {I : BoundaryInterval n} (hI : I.leaves = 1)
    (T : OpenPlaneTree I) : T = .leaf hI := by
  cases T with
  | leaf h => rfl
  | node π hp children =>
    have hk := π.part_leaves_lt hp (⟨0, π.parts_pos⟩ : Fin π.parts)
    have hkpos := (π.part (⟨0, π.parts_pos⟩ : Fin π.parts)).leaves_pos
    omega

theorem openPlaneTreeSum_one (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : I.leaves = 1) : openPlaneTreeSum ordinary I = 1 := by
  letI : Unique (OpenPlaneTree I) := ⟨⟨.leaf hI⟩, OpenPlaneTree.eq_leaf hI⟩
  rw [openPlaneTreeSum, Fintype.sum_unique, OpenPlaneTree.eq_leaf hI (default : OpenPlaneTree I)]
  rfl

/-- Ungrafting splits the finite sum into the top composition and all independent
ordered child choices. Distributivity changes the sum over those choices into
the product of the child sums. The single top minus is kept outside. -/
theorem openPlaneTreeSum_many (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) (hI : 2 ≤ I.leaves) :
    openPlaneTreeSum ordinary I =
      -∑ π : {π : IntervalComposition I // 2 ≤ π.parts},
        ordinary I π.val * ∏ k : Fin π.val.parts, openPlaneTreeSum ordinary (π.val.part k) := by
  classical
  letI : IsEmpty (PLift (I.leaves = 1)) := ⟨fun h => by have := h.down; omega⟩
  have hs := Fintype.sum_equiv (openPlaneTreeUngraft I)
    (OpenPlaneTree.weight ordinary)
    (Sum.elim (fun _ => (1 : R)) (fun v =>
      -ordinary I v.1.val * ∏ k, OpenPlaneTree.weight ordinary (v.2 k)))
    (by intro T; cases T <;> rfl)
  unfold openPlaneTreeSum
  rw [hs, Fintype.sum_sum_type]
  simp only [Finset.sum_of_isEmpty, zero_add, Fintype.sum_sigma, Sum.elim_inr]
  simp_rw [← Finset.mul_sum, ← Fintype.prod_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- The recursively defined open coefficient equals the sum over all actual
ordinary plane trees, proved by strict decrease of every child interval. -/
theorem openTreeRec_eq_planeTreeSum
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R) (I : BoundaryInterval n) :
    openTreeRec ordinary I = openPlaneTreeSum ordinary I := by
  by_cases hI : I.leaves = 1
  · rw [openTreeRec_one ordinary I hI, openPlaneTreeSum_one ordinary I hI]
  · have hm : 2 ≤ I.leaves := by have := I.leaves_pos; omega
    rw [openTreeRec_many ordinary I hm, openPlaneTreeSum_many ordinary I hm]
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    exact openTreeRec_eq_planeTreeSum ordinary (π.val.part k)
termination_by I.leaves
decreasing_by exact π.val.part_leaves_lt π.property k

/-- Grafting at the distinguished root allows every source composition,
including the single-child case, and inserts no ordinary-vertex sign. -/
theorem rootedTreeRec_eq_planeTreeSum
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    rootedTreeRec ordinary rootWeight I = ∑ T : RootedPlaneTree I, T.weight ordinary rootWeight := by
  classical
  unfold rootedTreeRec
  simp_rw [openTreeRec_eq_planeTreeSum, openPlaneTreeSum, Fintype.prod_sum, Finset.mul_sum]
  let e : (Σ π : IntervalComposition I, ∀ k : Fin π.parts, OpenPlaneTree (π.part k)) ≃
      RootedPlaneTree I := Equiv.refl _
  calc
    _ = ∑ T : (Σ π : IntervalComposition I, ∀ k : Fin π.parts, OpenPlaneTree (π.part k)),
        rootWeight I T.1 * ∏ k, OpenPlaneTree.weight ordinary (T.2 k) :=
      (Fintype.sum_sigma (fun T : (Σ π : IntervalComposition I,
        ∀ k : Fin π.parts, OpenPlaneTree (π.part k)) =>
        rootWeight I T.1 * ∏ k, OpenPlaneTree.weight ordinary (T.2 k))).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The full signed vertex-product formula, valid for arbitrary independent
weights in every commutative ring. -/
theorem rootedTreeRec_eq_signed_planeTreeSum
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    rootedTreeRec ordinary rootWeight I = ∑ T : RootedPlaneTree I,
      (-1 : R) ^ T.ordinaryCount * rootWeight I T.fst * T.ordinaryProduct ordinary := by
  rw [rootedTreeRec_eq_planeTreeSum]
  apply Finset.sum_congr rfl
  intro T _
  exact T.weight_eq_signed_product ordinary rootWeight

end

end SM
