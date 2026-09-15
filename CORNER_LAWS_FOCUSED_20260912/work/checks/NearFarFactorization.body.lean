namespace SM

noncomputable section
variable {n : ℕ} [NeZero n] {I : BoundaryInterval n}

/-- Transporting a marking between equal cut sets preserves its physical positions. -/
theorem BoundaryCutSet.marked_transport_val {S T : BoundaryCutSet I} (h : S = T)
    (m : MarkedCuts S) : (h ▸ m : MarkedCuts T).val = m.val := by
  subst T
  rfl

namespace IntervalComposition

/-- The full marked-refinement equivalence records exactly the outer interior
cuts as marks, including when the final dependent marking type is transported. -/
theorem nestedMarkedCutEquiv_marks (π : IntervalComposition I)
    (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    (nestedMarkedCutEquiv I ⟨π, σ⟩).2.val = π.cutSet.interior.val := by
  let T := π.flattenCutSets (fun k => (σ k).cutSet)
  let m : MarkedCuts T := ⟨π.cutSet.interior.val,
    (BoundaryCutSet.cuts_subset_iff_interior_subset π.cutSet T).mp
      (π.outer_cuts_subset_flatten (fun k => (σ k).cutSet))⟩
  change (T.toComposition_cutSet.symm ▸ m : MarkedCuts T.toComposition.cutSet).val = _
  exact BoundaryCutSet.marked_transport_val T.toComposition_cutSet.symm m

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- One summand in the actual expanded composite F_H(G_D(X)). -/
def nestedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) : R :=
  π.nearFarWeight 0 H * ∏ k : Fin π.parts,
    (σ k).nearFarWeight D 0 * ∏ j : Fin (σ k).parts, X ((σ k).part j)

/-- One refined summand for an arbitrary set of physical marked cuts. -/
def markedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (ρ : IntervalComposition I) (m : MarkedCuts ρ.cutSet) : R :=
  ((∏ r ∈ ρ.markIndices m, -H (ρ.farTriple r) * ⅟ (2 : R)) *
    (∏ r ∈ (ρ.markIndices m)ᶜ, D (ρ.nearTriple r) * ⅟ (2 : R))) *
      ∏ j : Fin ρ.parts, X (ρ.part j)

/-- The actual source indexing equivalence preserves the complete summand
for any original family of raw inner compositions. -/
theorem nestedSummand_eq_markedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (π : IntervalComposition I) (σ : ∀ k : Fin π.parts, IntervalComposition (π.part k)) :
    nestedSummand D H X π σ =
      markedSummand D H X (nestedMarkedCutEquiv I ⟨π, σ⟩).1
        (nestedMarkedCutEquiv I ⟨π, σ⟩).2 := by
  let T := π.flattenRefinement (fun k => (σ k).cutSet)
  have hm : (nestedMarkedCutEquiv I ⟨π, σ⟩).2 = π.refinementMarks T :=
    Subtype.ext (π.nestedMarkedCutEquiv_marks σ)
  rw [hm]
  have ht : (fun k => π.refinementInner T k) = σ :=
    funext (π.refinementInner_flatten σ)
  have hp := π.nested_summand_transport T D H X
  have hh := congrArg (fun η : ∀ k : Fin π.parts, IntervalComposition (π.part k) =>
    ∏ k : Fin π.parts, (η k).nearFarWeight D 0 *
      ∏ j : Fin (η k).parts, X ((η k).part j)) ht
  rw [hh] at hp
  exact hp

/-- Summing every possible marking produces the original near-far weight,
with the refined child-coordinate product held fixed. -/
theorem sum_markedSummand (D H : TripleArray n R) (X : IntervalArray n R)
    (ρ : IntervalComposition I) :
    (∑ m : MarkedCuts ρ.cutSet, markedSummand D H X ρ m) =
      ρ.nearFarWeight D H * ∏ j : Fin ρ.parts, X (ρ.part j) := by
  rw [← ρ.sum_all_indexMarks (markedSummand D H X ρ)]
  simp only [markedSummand, markIndices_indexMarks]
  rw [← Finset.sum_mul, ← nearFarWeight_marked_expansion]

end IntervalComposition

open IntervalComposition
variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Source factorization on every interval, over the full allowed coefficient
ring and all arrays. Distributivity expands the actual composite; the exact
source equivalence reindexes its full summands; all markings then recombine. -/
theorem nearFar_factorization_coordinate (D H : TripleArray n R)
    (X : IntervalArray n R) (I : BoundaryInterval n) :
    farTransform H (nearTransform D X) I = nearFarTransform D H X I := by
  classical
  calc
    farTransform H (nearTransform D X) I =
        ∑ π : IntervalComposition I,
          ∑ σ : ∀ k : Fin π.parts, IntervalComposition (π.part k), nestedSummand D H X π σ := by
      simp only [farTransform, nearTransform, nearFarTransform, Fintype.prod_sum,
        Finset.mul_sum, nestedSummand]
    _ = ∑ a : (Σ π : IntervalComposition I,
        ∀ k : Fin π.parts, IntervalComposition (π.part k)), nestedSummand D H X a.1 a.2 :=
      (Fintype.sum_sigma' (nestedSummand D H X)).symm
    _ = ∑ b : (Σ ρ : IntervalComposition I, MarkedCuts ρ.cutSet),
        markedSummand D H X b.1 b.2 :=
      Fintype.sum_equiv (nestedMarkedCutEquiv I) _ _
        (fun a => nestedSummand_eq_markedSummand D H X a.1 a.2)
    _ = ∑ ρ : IntervalComposition I, ∑ m : MarkedCuts ρ.cutSet,
        markedSummand D H X ρ m := Fintype.sum_sigma' (markedSummand D H X)
    _ = ∑ ρ : IntervalComposition I,
        ρ.nearFarWeight D H * ∏ j : Fin ρ.parts, X (ρ.part j) := by
      apply Finset.sum_congr rfl
      intro ρ _
      exact sum_markedSummand D H X ρ
    _ = nearFarTransform D H X I := rfl

/-- The complete source transform is the far-only transform composed with
the near-only transform; this is an equality of the full polynomial maps. -/
theorem nearFar_factorization (D H : TripleArray n R) :
    nearFarTransform D H = farTransform H ∘ nearTransform D := by
  funext X I
  exact (nearFar_factorization_coordinate D H X I).symm

end
end SM
