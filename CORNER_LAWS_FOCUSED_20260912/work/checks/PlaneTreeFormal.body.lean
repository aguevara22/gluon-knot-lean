namespace SM

noncomputable section

universe u v
variable {n : ℕ} [NeZero n] {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism preserves every actual finite tree evaluation. -/
theorem OpenPlaneTree.map_weight (f : R →+* S)
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    f (T.weight ordinary) = T.weight (fun J π => f (ordinary J π)) := by
  induction T with
  | leaf hI => simp [OpenPlaneTree.weight]
  | node π hp children ih => simp [OpenPlaneTree.weight, map_prod, ih]

theorem RootedPlaneTree.map_weight (f : R →+* S)
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    f (T.weight ordinary rootWeight) =
      T.weight (fun J π => f (ordinary J π)) (fun J π => f (rootWeight J π)) := by
  simp [RootedPlaneTree.weight, map_prod, OpenPlaneTree.map_weight]

theorem map_rootedTreeRec (f : R →+* S)
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    (I : BoundaryInterval n) :
    f (rootedTreeRec ordinary rootWeight I) =
      rootedTreeRec (fun J π => f (ordinary J π)) (fun J π => f (rootWeight J π)) I := by
  rw [rootedTreeRec_eq_planeTreeSum, map_sum, rootedTreeRec_eq_planeTreeSum]
  apply Finset.sum_congr rfl
  intro T _
  exact T.map_weight f ordinary rootWeight

/-- Separate variables for the ordinary and distinguished-root weights of every
actual interval composition. No geometric gate relation is imposed. -/
abbrev TreeWeightIndex (n : ℕ) := Bool × (Σ I : BoundaryInterval n, IntervalComposition I)

def formalOrdinaryWeight (I : BoundaryInterval n) (π : IntervalComposition I) :
    MvPolynomial (TreeWeightIndex n) ℤ := MvPolynomial.X (false, ⟨I, π⟩)

def formalRootWeight (I : BoundaryInterval n) (π : IntervalComposition I) :
    MvPolynomial (TreeWeightIndex n) ℤ := MvPolynomial.X (true, ⟨I, π⟩)

theorem planeTree_formal_identity (I : BoundaryInterval n) :
    rootedTreeRec formalOrdinaryWeight formalRootWeight I =
      ∑ T : RootedPlaneTree I, (-1 : MvPolynomial (TreeWeightIndex n) ℤ) ^ T.ordinaryCount *
        formalRootWeight I T.fst * T.ordinaryProduct formalOrdinaryWeight :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ I

/-- The formal polynomial evaluates to the same recursion for every assignment
of its independent variables in any commutative ring. -/
theorem planeTree_formal_evaluation (I : BoundaryInterval n) (values : TreeWeightIndex n → S) :
    MvPolynomial.eval₂Hom (Int.castRingHom S) values
        (rootedTreeRec formalOrdinaryWeight formalRootWeight I) =
      rootedTreeRec (fun J π => values (false, ⟨J, π⟩))
        (fun J π => values (true, ⟨J, π⟩)) I := by
  simpa only [formalOrdinaryWeight, formalRootWeight, MvPolynomial.eval₂Hom_X'] using
    map_rootedTreeRec (MvPolynomial.eval₂Hom (Int.castRingHom S) values)
      formalOrdinaryWeight formalRootWeight I

theorem treeCoefficient_eq_signed_planeTreeSum (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : ℤ) ^ T.ordinaryCount * T.fst.rootWeight P hP g *
        T.ordinaryProduct (fun _ π => π.ordinaryWeight P hP g) :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ _

/-- All clauses of source lem:treesum-trees: actual gate evaluation, the
independent-variable identity over integers, and every ring evaluation. The
separate ungrafting equivalence records the term-by-term tree correspondence. -/
theorem treesum_trees (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) (hn : 3 ≤ n) :
    (treeCoefficient P hP g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : ℤ) ^ T.ordinaryCount * T.fst.rootWeight P hP g *
        T.ordinaryProduct (fun _ π => π.ordinaryWeight P hP g)) ∧
    (rootedTreeRec formalOrdinaryWeight formalRootWeight (fullBoundaryInterval hn) =
      ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
        (-1 : MvPolynomial (TreeWeightIndex n) ℤ) ^ T.ordinaryCount *
          formalRootWeight (fullBoundaryInterval hn) T.fst * T.ordinaryProduct formalOrdinaryWeight) ∧
    (∀ (A : Type v) [CommRing A] (values : TreeWeightIndex n → A),
      MvPolynomial.eval₂Hom (Int.castRingHom A) values
          (rootedTreeRec formalOrdinaryWeight formalRootWeight (fullBoundaryInterval hn)) =
        rootedTreeRec (fun J π => values (false, ⟨J, π⟩))
          (fun J π => values (true, ⟨J, π⟩)) (fullBoundaryInterval hn)) :=
  ⟨treeCoefficient_eq_signed_planeTreeSum P hP g hn,
    planeTree_formal_identity _, fun _ _ values => planeTree_formal_evaluation _ values⟩

end

end SM
