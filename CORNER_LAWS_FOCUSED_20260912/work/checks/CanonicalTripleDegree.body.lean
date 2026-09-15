namespace SM

noncomputable section
open scoped Classical
variable {n : ℕ} [NeZero n]

/-- Transport actual unordered boundary supports to canonical physical variables. -/
def canonicalSupport (g : ZMod n) (S : Finset (IncreasingBoundaryTriple n)) :
    Finset (IncreasingBoundaryTriple n) := by
  classical
  exact S.image (fun t => (boundaryTripleData g t).1)

theorem canonicalSupport_mono (g : ZMod n) {S T : Finset (IncreasingBoundaryTriple n)}
    (hST : S ⊆ T) : canonicalSupport g S ⊆ canonicalSupport g T := by
  classical
  exact Finset.image_subset_image hST

theorem canonicalSupport_disjoint (g : ZMod n) {S T : Finset (IncreasingBoundaryTriple n)}
    (hST : Disjoint S T) : Disjoint (canonicalSupport g S) (canonicalSupport g T) := by
  classical
  exact (Finset.disjoint_image (boundaryTripleData_injective g)).mpr hST

theorem canonicalSupport_union (g : ZMod n) (S T : Finset (IncreasingBoundaryTriple n)) :
    canonicalSupport g (S ∪ T) = canonicalSupport g S ∪ canonicalSupport g T := by
  classical
  exact Finset.image_union _ _

theorem canonicalSupport_biUnion {ι : Type*} (g : ZMod n) (s : Finset ι)
    (S : ι → Finset (IncreasingBoundaryTriple n)) :
    canonicalSupport g (s.biUnion S) = s.biUnion (fun i => canonicalSupport g (S i)) := by
  classical
  exact Finset.biUnion_image

theorem formalBoundaryChi_supported (g : ZMod n) (t : IncreasingBoundaryTriple n) :
    SupportedMultiaffine (formalBoundaryChi g t) (canonicalSupport g {t}) := by
  classical
  rw [formalBoundaryChi_eq]
  simpa only [canonicalSupport, Finset.image_singleton] using
    (SupportedMultiaffine.X_singleton (boundaryTripleData g t).1).constant_mul
      (boundaryTripleData g t).2

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- All sampled boundary triples at this actual node. -/
def tripleSupport : Finset (IncreasingBoundaryTriple n) := by
  classical
  exact Finset.univ.biUnion π.cutTripleSet

theorem mem_tripleSupport (t : IncreasingBoundaryTriple n) :
    t ∈ π.tripleSupport ↔ ∃ k, t ∈ π.cutTripleSet k := by
  classical
  simp [tripleSupport]

theorem tripleFactors_supported (g : ZMod n) (k : Fin (π.parts - 1)) :
    SupportedMultiaffine (π.tripleOrdinaryFactor g k) (canonicalSupport g (π.cutTripleSet k)) ∧
      SupportedMultiaffine (π.tripleRootFactor g k) (canonicalSupport g (π.cutTripleSet k)) := by
  classical
  have hn := (formalBoundaryChi_supported g (π.nearTriple k)).mono
    (canonicalSupport_mono g (show {π.nearTriple k} ⊆ π.cutTripleSet k by
      intro t ht
      have he := Finset.mem_singleton.mp ht
      subst t
      exact (π.mem_cutTripleSet k _).mpr (Or.inl rfl)))
  have hf := (formalBoundaryChi_supported g (π.farTriple k)).mono
    (canonicalSupport_mono g (show {π.farTriple k} ⊆ π.cutTripleSet k by
      intro t ht
      have he := Finset.mem_singleton.mp ht
      subst t
      exact (π.mem_cutTripleSet k _).mpr (Or.inr rfl)))
  exact ⟨(hn.sub hf).constant_mul (1 / 2), (hn.add hf).constant_mul (1 / 2)⟩

theorem tripleWeights_supported (g : ZMod n) :
    SupportedMultiaffine (π.tripleOrdinaryWeight g) (canonicalSupport g π.tripleSupport) ∧
      SupportedMultiaffine (π.tripleRootWeight g) (canonicalSupport g π.tripleSupport) := by
  classical
  have hd : Pairwise (fun k l : Fin (π.parts - 1) =>
      Disjoint (canonicalSupport g (π.cutTripleSet k)) (canonicalSupport g (π.cutTripleSet l))) :=
    fun _ _ h => canonicalSupport_disjoint g (π.cutTripleSet_disjoint h)
  constructor
  · simpa only [tripleOrdinaryWeight, tripleSupport, canonicalSupport_biUnion] using
      SupportedMultiaffine.prod Finset.univ (π.tripleOrdinaryFactor g)
        (fun k => canonicalSupport g (π.cutTripleSet k))
        (fun k => (π.tripleFactors_supported g k).1) hd
  · simpa only [tripleRootWeight, tripleSupport, canonicalSupport_biUnion] using
      SupportedMultiaffine.prod Finset.univ (π.tripleRootFactor g)
        (fun k => canonicalSupport g (π.cutTripleSet k))
        (fun k => (π.tripleFactors_supported g k).2) hd

theorem tripleSupport_disjoint_child_support
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j)) (j : Fin π.parts) :
    Disjoint π.tripleSupport (children j).tripleSupport := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hu
  obtain ⟨k, hk⟩ := (π.mem_tripleSupport t).mp ht
  exact (Finset.disjoint_left.mp (π.cutTripleSet_disjoint_child_support children k j)) hk hu

theorem tripleSupport_disjoint_children_support
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j)) :
    Disjoint π.tripleSupport (Finset.univ.biUnion (fun j => (children j).tripleSupport)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hu
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hu
  exact (Finset.disjoint_left.mp (π.tripleSupport_disjoint_child_support children j)) ht hj

end IntervalComposition

/-- Actual-tree nonrepetition transported to the source's physical variable
set, independently of geometric evaluation or realizability. -/
theorem RootedPlaneTree.canonical_cut_nonrepetition {I : BoundaryInterval n}
    (T : RootedPlaneTree I) (g : ZMod n) {a b : T.CutOccurrence}
    {t : IncreasingBoundaryTriple n}
    (ha : t ∈ canonicalSupport g (T.cutTripleSupport a))
    (hb : t ∈ canonicalSupport g (T.cutTripleSupport b)) : a = b := by
  classical
  by_contra h
  exact (Finset.disjoint_left.mp
    (canonicalSupport_disjoint g (T.cutTripleSupport_pairwise h))) ha hb

end
end SM
