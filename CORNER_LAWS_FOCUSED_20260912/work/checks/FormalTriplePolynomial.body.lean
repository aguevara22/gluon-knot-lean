namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Rational gate identities are proved directly on all four nonzero sign
pairs; integer division is not transported through a cast. -/
theorem gate_pair_rational (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : ℚ) = (1 / 2 : ℚ) * ((d : ℤ) - (h : ℤ)) ∧
    (rootGate d h hd hh : ℚ) = (1 / 2 : ℚ) * ((d : ℤ) + (h : ℤ)) := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

namespace IntervalComposition
variable {I : BoundaryInterval n} (π : IntervalComposition I)

/-- Source ordinary half-difference, in independent canonical triple variables. -/
def tripleOrdinaryFactor (g : ZMod n) (k : Fin (π.parts - 1)) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) *
    (formalBoundaryChi g (π.nearTriple k) - formalBoundaryChi g (π.farTriple k))

/-- Source root half-sum, with the same physical root reading. -/
def tripleRootFactor (g : ZMod n) (k : Fin (π.parts - 1)) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) *
    (formalBoundaryChi g (π.nearTriple k) + formalBoundaryChi g (π.farTriple k))

def tripleOrdinaryWeight (g : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  ∏ k : Fin (π.parts - 1), π.tripleOrdinaryFactor g k

def tripleRootWeight (g : ZMod n) : MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  ∏ k : Fin (π.parts - 1), π.tripleRootFactor g k

theorem tripleFactors_binary (g : ZMod n) (hp : π.parts = 2) (k : Fin (π.parts - 1)) :
    π.tripleOrdinaryFactor g k = 0 ∧
      π.tripleRootFactor g k = formalBoundaryChi g (π.nearTriple k) := by
  have he := (π.nearTriple_eq_farTriple_iff k k).mpr ⟨hp, rfl⟩
  have hc : (MvPolynomial.C (1 / 2 : ℚ) : MvPolynomial (IncreasingBoundaryTriple n) ℚ) +
      MvPolynomial.C (1 / 2 : ℚ) = 1 := by
    rw [← map_add]
    norm_num
  constructor
  · simp only [tripleOrdinaryFactor, he, sub_self, mul_zero]
  · unfold tripleRootFactor
    rw [← he]
    calc
      _ = (MvPolynomial.C (1 / 2 : ℚ) + MvPolynomial.C (1 / 2 : ℚ)) *
          formalBoundaryChi g (π.nearTriple k) := by ring
      _ = formalBoundaryChi g (π.nearTriple k) := by rw [hc, one_mul]

theorem tripleWeights_unary (g : ZMod n) (hp : π.parts = 1) :
    π.tripleOrdinaryWeight g = 1 ∧ π.tripleRootWeight g = 1 := by
  letI : IsEmpty (Fin (π.parts - 1)) := ⟨fun k => by have := k.isLt; omega⟩
  simp [tripleOrdinaryWeight, tripleRootWeight]

theorem tripleOrdinaryWeight_binary (g : ZMod n) (hp : π.parts = 2) :
    π.tripleOrdinaryWeight g = 0 := by
  let k : Fin (π.parts - 1) := ⟨0, by omega⟩
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  exact (π.tripleFactors_binary g hp k).1

theorem tripleRootWeight_binary (g : ZMod n) (hp : π.parts = 2)
    (k : Fin (π.parts - 1)) :
    π.tripleRootWeight g = formalBoundaryChi g (π.nearTriple k) := by
  calc
    _ = π.tripleRootFactor g k := by
      apply Finset.prod_eq_single k
      · intro l _ hl
        exfalso
        apply hl
        apply Fin.ext
        have := l.isLt
        have := k.isLt
        omega
      · simp
    _ = _ := (π.tripleFactors_binary g hp k).2

theorem eval_tripleOrdinaryFactor (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleOrdinaryFactor g k) =
      (ordinaryGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k) : ℚ) := by
  rw [tripleOrdinaryFactor, map_mul, MvPolynomial.eval_C, map_sub,
    eval_formalBoundaryChi, eval_formalBoundaryChi]
  exact (gate_pair_rational _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).1.symm

theorem eval_tripleRootFactor (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (k : Fin (π.parts - 1)) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleRootFactor g k) =
      (rootGate (π.nearSign P g k) (π.farSign P g k)
        (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k) : ℚ) := by
  rw [tripleRootFactor, map_mul, MvPolynomial.eval_C, map_add,
    eval_formalBoundaryChi, eval_formalBoundaryChi]
  exact (gate_pair_rational _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).2.symm

theorem eval_tripleOrdinaryWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleOrdinaryWeight g) =
      (π.ordinaryWeight P hP g : ℚ) := by
  simp only [tripleOrdinaryWeight, ordinaryWeight, map_prod, Int.cast_prod,
    eval_tripleOrdinaryFactor π P hP g]

theorem eval_tripleRootWeight (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    MvPolynomial.eval (canonicalTripleValue P) (π.tripleRootWeight g) =
      (π.rootWeight P hP g : ℚ) := by
  simp only [tripleRootWeight, rootWeight, map_prod, Int.cast_prod,
    eval_tripleRootFactor π P hP g]

end IntervalComposition

/-- Exactly the polynomial prescribed by the finite rooted tree recursion,
using signed canonical physical triple variables for each original cut. -/
def canonicalTreePolynomial (g : ZMod n) (hn : 3 ≤ n) :
    MvPolynomial (IncreasingBoundaryTriple n) ℚ :=
  rootedTreeRec (fun _ π => π.tripleOrdinaryWeight g)
    (fun _ π => π.tripleRootWeight g) (fullBoundaryInterval hn)

/-- The actual signed finite-tree sum, without independent composition variables. -/
theorem canonicalTreePolynomial_eq_signed_tree_sum (g : ZMod n) (hn : 3 ≤ n) :
    canonicalTreePolynomial g hn = ∑ T : RootedPlaneTree (fullBoundaryInterval hn),
      (-1 : MvPolynomial (IncreasingBoundaryTriple n) ℚ) ^ T.ordinaryCount *
        T.fst.tripleRootWeight g * T.ordinaryProduct (fun _ π => π.tripleOrdinaryWeight g) :=
  rootedTreeRec_eq_signed_planeTreeSum _ _ _

/-- Exact G1 evaluation of the prescribed polynomial at the same physical root.
This theorem does not yet assert its individual-variable degree bound. -/
theorem eval_canonicalTreePolynomial (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    MvPolynomial.eval (canonicalTripleValue P) (canonicalTreePolynomial g hn) =
      (treeCoefficient P hP g hn : ℚ) := by
  unfold canonicalTreePolynomial
  rw [map_rootedTreeRec]
  change rootedTreeRec _ _ _ = (Int.castRingHom ℚ) (rootedTreeRec _ _ _)
  rw [map_rootedTreeRec]
  congr 1
  · funext I π
    exact π.eval_tripleOrdinaryWeight P hP g
  · funext I π
    exact π.eval_tripleRootWeight P hP g

end
end SM
