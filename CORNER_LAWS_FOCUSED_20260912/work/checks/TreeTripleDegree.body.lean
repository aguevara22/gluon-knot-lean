namespace SM

noncomputable section
open scoped Classical
variable {n : ℕ} [NeZero n]

theorem OpenPlaneTree.tripleSupport_node {I : BoundaryInterval n}
    (π : IntervalComposition I) (hp : 2 ≤ π.parts)
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j)) :
    (OpenPlaneTree.node π hp children).tripleSupport =
      π.tripleSupport ∪ Finset.univ.biUnion (fun j => (children j).tripleSupport) := by
  ext t
  constructor
  · intro ht
    obtain ⟨o, ho⟩ := ((OpenPlaneTree.node π hp children).mem_tripleSupport t).mp ht
    rcases o with k | ⟨j, o⟩
    · exact Finset.mem_union_left _ ((π.mem_tripleSupport t).mpr ⟨k, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, ((children j).mem_tripleSupport t).mpr ⟨o, ho⟩⟩)
  · intro ht
    apply ((OpenPlaneTree.node π hp children).mem_tripleSupport t).mpr
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨k, hk⟩ := (π.mem_tripleSupport t).mp ht
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨o, ho⟩ := ((children j).mem_tripleSupport t).mp hj
      exact ⟨Sum.inr ⟨j, o⟩, ho⟩

theorem RootedPlaneTree.tripleSupport_eq {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.tripleSupport = T.fst.tripleSupport ∪
      Finset.univ.biUnion (fun j => (T.snd j).tripleSupport) := by
  ext t
  constructor
  · intro ht
    obtain ⟨o, ho⟩ := (T.mem_tripleSupport t).mp ht
    rcases o with k | ⟨j, o⟩
    · exact Finset.mem_union_left _ ((T.fst.mem_tripleSupport t).mpr ⟨k, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, ((T.snd j).mem_tripleSupport t).mpr ⟨o, ho⟩⟩)
  · intro ht
    apply (T.mem_tripleSupport t).mpr
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨k, hk⟩ := (T.fst.mem_tripleSupport t).mp ht
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨o, ho⟩ := ((T.snd j).mem_tripleSupport t).mp hj
      exact ⟨Sum.inr ⟨j, o⟩, ho⟩

/-- Composition of supported polynomials on the actual parent and children.
All disjointness is derived from actual tree intervals and cut supports. -/
theorem IntervalComposition.combine_supported {I : BoundaryInterval n}
    (π : IntervalComposition I) (g : ZMod n)
    (children : ∀ j : Fin π.parts, OpenPlaneTree (π.part j))
    (p : MvPolynomial (IncreasingBoundaryTriple n) ℚ)
    (q : Fin π.parts → MvPolynomial (IncreasingBoundaryTriple n) ℚ)
    (hp : SupportedMultiaffine p (canonicalSupport g π.tripleSupport))
    (hq : ∀ j, SupportedMultiaffine (q j) (canonicalSupport g (children j).tripleSupport)) :
    SupportedMultiaffine (p * ∏ j, q j)
      (canonicalSupport g (π.tripleSupport ∪
        Finset.univ.biUnion (fun j => (children j).tripleSupport))) := by
  have hdis : Pairwise (fun j k => Disjoint
      (canonicalSupport g (children j).tripleSupport)
      (canonicalSupport g (children k).tripleSupport)) :=
    fun _ _ h => canonicalSupport_disjoint g (π.children_tripleSupport_disjoint children h)
  have hprod := SupportedMultiaffine.prod Finset.univ q
    (fun j => canonicalSupport g (children j).tripleSupport) hq hdis
  have htop : Disjoint (canonicalSupport g π.tripleSupport)
      (Finset.univ.biUnion (fun j => canonicalSupport g (children j).tripleSupport)) := by
    rw [← canonicalSupport_biUnion]
    exact canonicalSupport_disjoint g (π.tripleSupport_disjoint_children_support children)
  simpa only [canonicalSupport_union, canonicalSupport_biUnion] using hp.mul_disjoint hprod htop

/-- Every actual ordinary tree weight is multi-affine, with zero degree
outside its derived canonical triple support, including zero binary weights. -/
theorem OpenPlaneTree.tripleWeight_supported {I : BoundaryInterval n}
    (T : OpenPlaneTree I) (g : ZMod n) :
    SupportedMultiaffine (T.weight (fun _ π => π.tripleOrdinaryWeight g))
      (canonicalSupport g T.tripleSupport) := by
  induction T with
  | leaf hI => exact SupportedMultiaffine.one _
  | node π hp children ih =>
      rw [OpenPlaneTree.weight, OpenPlaneTree.tripleSupport_node]
      exact π.combine_supported g children (-π.tripleOrdinaryWeight g)
        (fun j => (children j).weight (fun _ ρ => ρ.tripleOrdinaryWeight g))
        (π.tripleWeights_supported g).1.neg ih

/-- Every actual rooted tree weight has the same bound; the root may be unary. -/
theorem RootedPlaneTree.tripleWeight_supported {I : BoundaryInterval n}
    (T : RootedPlaneTree I) (g : ZMod n) :
    SupportedMultiaffine
      (T.weight (fun _ π => π.tripleOrdinaryWeight g) (fun _ π => π.tripleRootWeight g))
      (canonicalSupport g T.tripleSupport) := by
  rw [RootedPlaneTree.weight, T.tripleSupport_eq]
  exact T.fst.combine_supported g T.snd (T.fst.tripleRootWeight g)
    (fun j => (T.snd j).weight (fun _ π => π.tripleOrdinaryWeight g))
    (T.fst.tripleWeights_supported g).2 (fun j => (T.snd j).tripleWeight_supported g)

/-- The prescribed polynomial has individual degree at most one in every
independent canonical physical variable, in the unrestricted rational ring. -/
theorem canonicalTreePolynomial_multiaffine (g : ZMod n) (hn : 3 ≤ n)
    (t : IncreasingBoundaryTriple n) : (canonicalTreePolynomial g hn).degreeOf t ≤ 1 := by
  unfold canonicalTreePolynomial
  rw [rootedTreeRec_eq_planeTreeSum]
  apply le_trans (MvPolynomial.degreeOf_sum_le t Finset.univ _)
  exact Finset.sup_le (fun T _ => (T.tripleWeight_supported g).degree_le_one t)

end
end SM
