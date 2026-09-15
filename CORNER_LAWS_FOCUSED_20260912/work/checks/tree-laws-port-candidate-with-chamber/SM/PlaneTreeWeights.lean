import SM.PlaneTreeShape

namespace SM

noncomputable section

universe u
variable {n : ℕ} [NeZero n] {R : Type u} [CommRing R]

namespace OpenPlaneTree

/-- One minus sign for each ordinary internal vertex, with independent weights. -/
def weight (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R) :
    {I : BoundaryInterval n} → OpenPlaneTree I → R
  | _, .leaf _ => 1
  | I, .node π _ children => -ordinary I π * ∏ k, weight ordinary (children k)

def ordinaryCount : {I : BoundaryInterval n} → OpenPlaneTree I → ℕ
  | _, .leaf _ => 0
  | _, .node π _ children => 1 + ∑ k : Fin π.parts, ordinaryCount (children k)

/-- The product over actual ordinary vertices, before inserting its sign. -/
def ordinaryProduct (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R) :
    {I : BoundaryInterval n} → OpenPlaneTree I → R
  | _, .leaf _ => 1
  | I, .node π _ children => ordinary I π * ∏ k, ordinaryProduct ordinary (children k)

theorem weight_eq_signed_product
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : OpenPlaneTree I) :
    weight ordinary T = (-1 : R) ^ ordinaryCount T * ordinaryProduct ordinary T := by
  induction T with
  | leaf hI => simp [weight, ordinaryCount, ordinaryProduct]
  | node π hp children ih =>
    simp only [weight, ordinaryCount, ordinaryProduct]
    rw [Finset.prod_congr rfl (fun k _ => ih k), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, pow_add, pow_one]
    ring

end OpenPlaneTree

/-- The root carries its own weight and no extra minus sign. -/
def RootedPlaneTree.weight
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) : R :=
  rootWeight I T.fst * ∏ k, OpenPlaneTree.weight ordinary (T.snd k)

def RootedPlaneTree.ordinaryCount {I : BoundaryInterval n} (T : RootedPlaneTree I) : ℕ :=
  ∑ k, OpenPlaneTree.ordinaryCount (T.snd k)

def RootedPlaneTree.ordinaryProduct
    (ordinary : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) : R :=
  ∏ k, OpenPlaneTree.ordinaryProduct ordinary (T.snd k)

theorem RootedPlaneTree.weight_eq_signed_product
    (ordinary rootWeight : ∀ I : BoundaryInterval n, IntervalComposition I → R)
    {I : BoundaryInterval n} (T : RootedPlaneTree I) :
    T.weight ordinary rootWeight = (-1 : R) ^ T.ordinaryCount *
      rootWeight I T.fst * T.ordinaryProduct ordinary := by
  unfold weight ordinaryCount ordinaryProduct
  rw [Finset.prod_congr rfl (fun k _ => OpenPlaneTree.weight_eq_signed_product ordinary (T.snd k)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end

end SM
