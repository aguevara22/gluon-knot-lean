import SM.TreeReversal
import SM.UnaryComposition
import SM.BowTie

/-! Towards lem:A-small-values (sm-6-comparison.tex:5). Written 2026-09-13 by a Claude Code prover subagent of the pod executor
(workflow prove-transport-lane-2 / prove:small-values), checked with `lake env lean` (placeholder-free, standard axioms) and ported verbatim
from work/drafts/SmallValues.lean (only this header added and #print lines removed). -/

/-! lem:A-small-values (reference/SM/sm-6-comparison.tex:5-52): triangle and bow-tie values of the
tree coefficient. Written 2026-09-13 by a Claude Code prover subagent, checked with `lake env lean`
(placeholder-free, standard axioms).

Contents: cut-position bounds for interval compositions (`smallValues_left_add_le_cut`,
`smallValues_cut_add_le_right`), uniqueness of the all-leaves composition, the vanishing of every
two-leaf open sum, the two- and three-part root/ordinary weights as gate products; clause (i)
(`A_small_values_i`: common turn sign `τ` and `A_g = -τ` for every (G1) triangle); the general
(G1) quadrilateral formula eq:root-bowtie-recursion (`quad_treeCoefficient`), the bow-tie sign
table eq:root-bowtie-signs (`bowTie_treeCoefficient`) and clause (ii) (`A_small_values_ii`,
`A_small_values_ii_int`); `A_small_values` bundles both clauses. Labels are in `ZMod n` with the
source label `n ≡ 0`; the source's `σ` is `shift 1` and `σ^k` is `shift k`
(`smallValues_shift_iterate`). -/

namespace SM

noncomputable section

variable {n : ℕ} [NeZero n]

namespace IntervalComposition

variable {I : BoundaryInterval n} (π : IntervalComposition I)

omit [NeZero n] in
/-- The `k`-th cut of a composition lies at least `k` steps to the right of the left end. -/
theorem smallValues_left_add_le_cut :
    ∀ (k : ℕ) (hk : k < π.parts + 1), I.left.val + k ≤ (π.cut ⟨k, hk⟩).val := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : (⟨0, hk⟩ : Fin (π.parts + 1)) = 0 := rfl
    rw [h0, π.first]
    simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := π.strict (show (⟨k, by omega⟩ : Fin (π.parts + 1)) < ⟨k + 1, hk⟩ from
      Nat.lt_succ_self k)
    change (π.cut ⟨k, _⟩).val < (π.cut ⟨k + 1, hk⟩).val at h2
    omega

omit [NeZero n] in
/-- The `k`-th cut lies at least `parts - k` steps to the left of the right end. -/
theorem smallValues_cut_add_le_right :
    ∀ (j : ℕ) (hj : j ≤ π.parts), (π.cut ⟨π.parts - j, by omega⟩).val + j ≤ I.right.val := by
  intro j
  induction j with
  | zero =>
    intro hj
    have h0 : (⟨π.parts - 0, by omega⟩ : Fin (π.parts + 1)) = Fin.last π.parts := rfl
    rw [h0, π.last]
    simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := π.strict (show (⟨π.parts - (j + 1), by omega⟩ : Fin (π.parts + 1)) <
      ⟨π.parts - j, by omega⟩ from by change π.parts - (j + 1) < π.parts - j; omega)
    change (π.cut ⟨π.parts - (j + 1), _⟩).val < (π.cut ⟨π.parts - j, _⟩).val at h2
    omega

omit [NeZero n] in
/-- A composition with as many parts as leaves cuts at every boundary vertex. -/
theorem smallValues_cut_of_parts_eq_leaves (hp : π.parts = I.leaves) (k : ℕ)
    (hk : k < π.parts + 1) : (π.cut ⟨k, hk⟩).val = I.left.val + k := by
  have h1 := π.smallValues_left_add_le_cut k hk
  have h2 := π.smallValues_cut_add_le_right (π.parts - k) (by omega)
  have hkk : π.parts - (π.parts - k) = k := by omega
  have h3 : (⟨π.parts - (π.parts - k), by omega⟩ : Fin (π.parts + 1)) = ⟨k, hk⟩ := Fin.ext hkk
  rw [h3] at h2
  have hl := I.increasing
  change I.left.val < I.right.val at hl
  unfold BoundaryInterval.leaves at hp
  omega

omit [NeZero n] in
/-- Two compositions with as many parts as leaves coincide. -/
theorem smallValues_eq_of_parts_eq_leaves {ρ : IntervalComposition I}
    (hp : π.parts = I.leaves) (hr : ρ.parts = I.leaves) : π = ρ := by
  apply ext' (hp.trans hr.symm)
  intro k hk hk'
  apply Fin.ext
  rw [π.smallValues_cut_of_parts_eq_leaves hp k hk, ρ.smallValues_cut_of_parts_eq_leaves hr k hk']

omit [NeZero n] in
/-- On a two-leaf interval every nonunary composition has exactly two parts. -/
theorem smallValues_parts_eq_two (hI : I.leaves = 2) (hp : 2 ≤ π.parts) : π.parts = 2 := by
  have := π.parts_le_leaves
  omega

/-- The root weight of a two-part composition is its single (near = far) sign. -/
theorem smallValues_rootWeight_two (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (hp : π.parts = 2) :
    π.rootWeight P hP g = ((π.nearSign P g ⟨0, by omega⟩ : SignType) : ℤ) := by
  unfold rootWeight
  rw [Finset.prod_eq_single ⟨0, by omega⟩]
  · rw [(gate_pair_identities _ _ _ _).2, ← π.binary_near_eq_far P g hp ⟨0, by omega⟩]
    have hd := π.nearSign_ne_zero hP g ⟨0, by omega⟩
    rcases nonzero_sign_cases _ hd with h | h <;> rw [h] <;> decide
  · intro b _ hb
    exact absurd (Fin.ext (by have := b.isLt; omega)) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The root weight of a three-part composition is the product of its two root gates. -/
theorem smallValues_rootWeight_three (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (hp : π.parts = 3) :
    π.rootWeight P hP g =
      rootGate (π.nearSign P g ⟨0, by omega⟩) (π.farSign P g ⟨0, by omega⟩)
        (π.nearSign_ne_zero hP g _) (π.farSign_ne_zero hP g _) *
      rootGate (π.nearSign P g ⟨1, by omega⟩) (π.farSign P g ⟨1, by omega⟩)
        (π.nearSign_ne_zero hP g _) (π.farSign_ne_zero hP g _) := by
  unfold rootWeight
  apply Fintype.prod_eq_mul
  · intro h
    have := congrArg Fin.val h
    simp at this
  · intro x ⟨hx0, hx1⟩
    exfalso
    have hx := x.isLt
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
    · exact hx0 (Fin.ext h)
    · exact hx1 (Fin.ext h)

/-- The ordinary weight of a three-part composition is the product of its two ordinary gates. -/
theorem smallValues_ordinaryWeight_three (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (hp : π.parts = 3) :
    π.ordinaryWeight P hP g =
      ordinaryGate (π.nearSign P g ⟨0, by omega⟩) (π.farSign P g ⟨0, by omega⟩)
        (π.nearSign_ne_zero hP g _) (π.farSign_ne_zero hP g _) *
      ordinaryGate (π.nearSign P g ⟨1, by omega⟩) (π.farSign P g ⟨1, by omega⟩)
        (π.nearSign_ne_zero hP g _) (π.farSign_ne_zero hP g _) := by
  unfold ordinaryWeight
  apply Fintype.prod_eq_mul
  · intro h
    have := congrArg Fin.val h
    simp at this
  · intro x ⟨hx0, hx1⟩
    exfalso
    have hx := x.isLt
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
    · exact hx0 (Fin.ext h)
    · exact hx1 (Fin.ext h)

end IntervalComposition

/-- Source: "all two-leaf open sums vanish, because their near and far signs agree". -/
theorem smallValues_openTreeSum_two_leaves (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    (I : BoundaryInterval n) (hI : I.leaves = 2) : openTreeSum P hP g I = 0 := by
  rw [openTreeSum_many P hP g I (by omega)]
  rw [Finset.sum_eq_zero, neg_zero]
  intro π _
  rw [π.val.binary_ordinaryWeight_zero P hP g (π.val.smallValues_parts_eq_two hI π.property),
    zero_mul]

/-- The product over the parts of a composition whose parts are all leaves is `1`. -/
theorem smallValues_leaf_product (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    {I : BoundaryInterval n} (π : IntervalComposition I) (hp : π.parts = I.leaves) :
    ∏ k : Fin π.parts, openTreeSum P hP g (π.part k) = 1 := by
  apply Finset.prod_eq_one
  intro k _
  apply openTreeSum_one
  unfold BoundaryInterval.leaves IntervalComposition.part
  simp only
  rw [π.smallValues_cut_of_parts_eq_leaves hp k.succ.val k.succ.isLt,
    π.smallValues_cut_of_parts_eq_leaves hp k.castSucc.val k.castSucc.isLt]
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

/-! ### The triangle, clause (i) -/

section Triangle

/-- The unique two-part composition of the boundary word of a triangle (cuts at `0, 1, 2`). -/
def triangleBinaryComposition :
    IntervalComposition (fullBoundaryInterval (n := 3) (by norm_num)) where
  parts := 2
  parts_pos := by norm_num
  cut := fun k => ⟨k.val, by omega⟩
  strict := fun _ _ h => h
  first := rfl
  last := rfl

theorem triangle_full_leaves : (fullBoundaryInterval (n := 3) (by norm_num)).leaves = 2 := rfl

/-- The boundary word of a triangle has two leaves: its compositions are the unary one
and the binary one. -/
theorem triangle_composition_cases
    (π : IntervalComposition (fullBoundaryInterval (n := 3) (by norm_num))) :
    π = IntervalComposition.single _ ∨ π = triangleBinaryComposition := by
  have hle := π.parts_le_leaves
  have hpos := π.parts_pos
  rw [triangle_full_leaves] at hle
  rcases (show π.parts = 1 ∨ π.parts = 2 by omega) with h | h
  · exact Or.inl (π.eq_single_of_parts_eq_one h)
  · exact Or.inr (π.smallValues_eq_of_parts_eq_leaves h rfl)

theorem triangle_binary_ne_single :
    triangleBinaryComposition ≠ IntervalComposition.single _ := by
  intro h
  have := congrArg IntervalComposition.parts h
  exact absurd this (by decide)

/-- The binary root sign `d = χ(a_2, a_1, a_0)`, with `a_i = P (g + i + 1)` and `g + 3 = g`. -/
theorem triangleBinaryComposition_nearSign (P : LabelledTuple 3) (g : ZMod 3) :
    triangleBinaryComposition.nearSign P g ⟨0, by decide⟩ = chi P g (g + 2) (g + 1) := by
  have h3 : g + 2 + 1 = g := by
    rw [add_assoc, show (2 : ZMod 3) + 1 = 0 by decide, add_zero]
  simp only [IntervalComposition.nearSign, boundaryIndex, triangleBinaryComposition, Nat.zero_add,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, add_zero]
  rw [h3, add_assoc g 1 1, one_add_one_eq_two]

/-- The triangle tree coefficient at the root `g` is `χ(a_2, a_1, a_0) = χ(g, g+2, g+1)`. -/
theorem triangle_treeCoefficient (P : LabelledTuple 3) (hP : G1 P) (g : ZMod 3) :
    treeCoefficient P hP g (by norm_num) = ((chi P g (g + 2) (g + 1) : SignType) : ℤ) := by
  rw [treeCoefficient_eq, Fintype.sum_eq_single triangleBinaryComposition]
  · rw [triangleBinaryComposition.smallValues_rootWeight_two P hP g rfl,
      smallValues_leaf_product P hP g triangleBinaryComposition rfl, mul_one,
      triangleBinaryComposition_nearSign]
  · intro π hπ
    rcases triangle_composition_cases π with h | h
    · rw [h, ((IntervalComposition.single _).one_part_weights P hP g rfl).2, one_mul,
        IntervalComposition.single_product, smallValues_openTreeSum_two_leaves P hP g _ rfl]
    · exact absurd h hπ

/-- All three turns of a triangle agree (cyclic permutations of one triple). -/
theorem triangle_turn_eq (P : LabelledTuple 3) (i : ZMod 3) : turn P i = turn P 0 := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by decide +revert) with rfl | rfl | rfl
  · rfl
  · show chi P (1 - 1) 1 (1 + 1) = chi P (0 - 1) 0 (0 + 1)
    rw [show (1 : ZMod 3) - 1 = 0 by decide, show (1 : ZMod 3) + 1 = 2 by decide,
      show (0 : ZMod 3) - 1 = 2 by decide, show (0 : ZMod 3) + 1 = 1 by decide]
    exact chi_cyclic P 2 0 1
  · show chi P (2 - 1) 2 (2 + 1) = chi P (0 - 1) 0 (0 + 1)
    rw [show (2 : ZMod 3) - 1 = 1 by decide, show (2 : ZMod 3) + 1 = 0 by decide,
      show (0 : ZMod 3) - 1 = 2 by decide, show (0 : ZMod 3) + 1 = 1 by decide]
    rw [chi_cyclic P 0 1 2]
    exact chi_cyclic P 2 0 1

theorem triangle_turn_ne_zero (P : LabelledTuple 3) (hP : G1 P) : turn P 0 ≠ 0 :=
  hP _ _ _ (by decide) (by decide) (by decide)

/-- `χ(g, g+2, g+1) = -τ_{g+1} = -τ`. -/
theorem triangle_chi_eq_neg_turn (P : LabelledTuple 3) (g : ZMod 3) :
    chi P g (g + 2) (g + 1) = -turn P 0 := by
  rw [← triangle_turn_eq P (g + 1), turn, add_sub_cancel_right, add_assoc, one_add_one_eq_two,
    chi_swap_last]

/-- lem:A-small-values (i): for every labelled triangle satisfying (G1), all turns have a
common sign `τ`, and `A_g = -τ` at every physical root `g`. -/
theorem A_small_values_i (P : LabelledTuple 3) (hP : G1 P) :
    ∃ τ : SignType, τ ≠ 0 ∧ (∀ i, turn P i = τ) ∧
      ∀ g, treeCoefficient P hP g (by norm_num) = -(τ : ℤ) := by
  refine ⟨turn P 0, triangle_turn_ne_zero P hP, triangle_turn_eq P, fun g => ?_⟩
  rw [triangle_treeCoefficient, triangle_chi_eq_neg_turn]
  cases turn P 0 <;> decide

end Triangle

/-! ### The bow-tie, clause (ii) -/

section Quadrilateral

/-- Every two-part composition of a three-leaf interval has a two-leaf child. -/
theorem smallValues_binary_child_two_leaves {I : BoundaryInterval n} (hI : I.leaves = 3)
    (π : IntervalComposition I) (hp : π.parts = 2) :
    (π.part ⟨0, by omega⟩).leaves = 2 ∨ (π.part ⟨1, by omega⟩).leaves = 2 := by
  have hs := π.sum_part_leaves
  rw [Fintype.sum_eq_add ⟨0, by omega⟩ ⟨1, by omega⟩] at hs
  · have h0 := (π.part ⟨0, by omega⟩).leaves_pos
    have h1 := (π.part ⟨1, by omega⟩).leaves_pos
    omega
  · intro h
    have := congrArg Fin.val h
    simp at this
  · intro x ⟨hx0, hx1⟩
    exfalso
    have hx := x.isLt
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
    · exact hx0 (Fin.ext h)
    · exact hx1 (Fin.ext h)

/-- Source: "every two-part composition has a two-leaf child and vanishes". -/
theorem smallValues_binary_product_zero (P : LabelledTuple n) (hP : G1 P) (g : ZMod n)
    {I : BoundaryInterval n} (hI : I.leaves = 3) (π : IntervalComposition I) (hp : π.parts = 2) :
    ∏ k : Fin π.parts, openTreeSum P hP g (π.part k) = 0 := by
  rcases smallValues_binary_child_two_leaves hI π hp with h | h
  · exact Finset.prod_eq_zero (Finset.mem_univ _) (smallValues_openTreeSum_two_leaves P hP g _ h)
  · exact Finset.prod_eq_zero (Finset.mem_univ _) (smallValues_openTreeSum_two_leaves P hP g _ h)

/-- The all-leaves composition of the boundary word of a quadrilateral (cuts at `0, 1, 2, 3`). -/
def quadTernaryComposition :
    IntervalComposition (fullBoundaryInterval (n := 4) (by norm_num)) where
  parts := 3
  parts_pos := by norm_num
  cut := fun k => ⟨k.val, by omega⟩
  strict := fun _ _ h => h
  first := rfl
  last := rfl

theorem quad_full_leaves : (fullBoundaryInterval (n := 4) (by norm_num)).leaves = 3 := rfl

/-- The compositions of a three-leaf boundary word: unary, two-part, or the all-leaves one. -/
theorem quad_composition_cases
    (π : IntervalComposition (fullBoundaryInterval (n := 4) (by norm_num))) :
    π = IntervalComposition.single _ ∨ π.parts = 2 ∨ π = quadTernaryComposition := by
  have hle := π.parts_le_leaves
  have hpos := π.parts_pos
  rw [quad_full_leaves] at hle
  rcases (show π.parts = 1 ∨ π.parts = 2 ∨ π.parts = 3 by omega) with h | h | h
  · exact Or.inl (π.eq_single_of_parts_eq_one h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (π.smallValues_eq_of_parts_eq_leaves h rfl))

/-- The unary root term is minus the ordinary three-part gate product. -/
theorem quad_openTreeSum_full (P : LabelledTuple 4) (hP : G1 P) (g : ZMod 4) :
    openTreeSum P hP g (fullBoundaryInterval (by norm_num)) =
      -quadTernaryComposition.ordinaryWeight P hP g := by
  rw [openTreeSum_many P hP g _ (by rw [quad_full_leaves]; norm_num)]
  congr 1
  rw [Fintype.sum_eq_single ⟨quadTernaryComposition, by show 2 ≤ 3; norm_num⟩]
  · rw [smallValues_leaf_product P hP g quadTernaryComposition rfl, mul_one]
  · intro π hπ
    rcases quad_composition_cases π.val with h | h | h
    · exfalso
      have := π.property
      rw [h] at this
      exact absurd this (by show ¬ 2 ≤ 1; norm_num)
    · rw [smallValues_binary_product_zero P hP g rfl π.val h, mul_zero]
    · exact absurd (Subtype.ext h) hπ

/-- The tree coefficient of a (G1) quadrilateral: the three-part root term minus the
ordinary three-part gate product. -/
theorem quad_treeCoefficient_weights (P : LabelledTuple 4) (hP : G1 P) (g : ZMod 4) :
    treeCoefficient P hP g (by norm_num) =
      quadTernaryComposition.rootWeight P hP g - quadTernaryComposition.ordinaryWeight P hP g := by
  rw [treeCoefficient_eq, Fintype.sum_eq_add (IntervalComposition.single _) quadTernaryComposition]
  · rw [((IntervalComposition.single _).one_part_weights P hP g rfl).2, one_mul,
      IntervalComposition.single_product, quad_openTreeSum_full,
      smallValues_leaf_product P hP g quadTernaryComposition rfl, mul_one]
    ring
  · intro h
    have := congrArg IntervalComposition.parts h
    exact absurd this (by show (1 : ℕ) ≠ 3; norm_num)
  · intro π ⟨h1, h3⟩
    rcases quad_composition_cases π with h | h | h
    · exact absurd h h1
    · rw [smallValues_binary_product_zero P hP g rfl π h, mul_zero]
    · exact absurd h h3

/-- `d₁ = χ(a_2, a_1, a_0)` with `a_i = P (g + i + 1)`. -/
theorem quadTernaryComposition_nearSign_zero (P : LabelledTuple 4) (g : ZMod 4) :
    quadTernaryComposition.nearSign P g ⟨0, by decide⟩ = chi P (g + 3) (g + 2) (g + 1) := by
  simp only [IntervalComposition.nearSign, boundaryIndex, quadTernaryComposition,
    fullBoundaryInterval, Nat.reduceAdd, Nat.reduceSub]
  push_cast
  congr 1 <;> ring1

/-- `d₂ = χ(a_3, a_2, a_1)`, where `a_3 = P (g + 4) = P g`. -/
theorem quadTernaryComposition_nearSign_one (P : LabelledTuple 4) (g : ZMod 4) :
    quadTernaryComposition.nearSign P g ⟨1, by decide⟩ = chi P g (g + 3) (g + 2) := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  simp only [IntervalComposition.nearSign, boundaryIndex, quadTernaryComposition,
    fullBoundaryInterval, Nat.reduceAdd, Nat.reduceSub]
  push_cast
  congr 1 <;> first | ring1 | linear_combination h4

/-- `h₁ = χ(a_3, a_1, a_0)`. -/
theorem quadTernaryComposition_farSign_zero (P : LabelledTuple 4) (g : ZMod 4) :
    quadTernaryComposition.farSign P g ⟨0, by decide⟩ = chi P g (g + 2) (g + 1) := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  simp only [IntervalComposition.farSign, boundaryIndex, quadTernaryComposition,
    fullBoundaryInterval, Nat.reduceAdd, Nat.reduceSub]
  push_cast
  congr 1 <;> first | ring1 | linear_combination h4

/-- `h₂ = χ(a_3, a_2, a_0)`. -/
theorem quadTernaryComposition_farSign_one (P : LabelledTuple 4) (g : ZMod 4) :
    quadTernaryComposition.farSign P g ⟨1, by decide⟩ = chi P g (g + 3) (g + 1) := by
  have h4 : (4 : ZMod 4) = 0 := by decide
  simp only [IntervalComposition.farSign, boundaryIndex, quadTernaryComposition,
    fullBoundaryInterval, Nat.reduceAdd, Nat.reduceSub]
  push_cast
  congr 1 <;> first | ring1 | linear_combination h4

/-- The two-gate identity behind eq:root-bowtie-recursion: on nonzero signs,
`V⁻ - V⁺ = ((d₁+h₁)(d₂+h₂) - (d₁-h₁)(d₂-h₂))/4 = (d₁h₂ + h₁d₂)/2` (exact integer divisions). -/
theorem smallValues_gate_formula (d₁ h₁ d₂ h₂ : SignType) (hd₁ : d₁ ≠ 0) (hh₁ : h₁ ≠ 0)
    (hd₂ : d₂ ≠ 0) (hh₂ : h₂ ≠ 0) :
    rootGate d₁ h₁ hd₁ hh₁ * rootGate d₂ h₂ hd₂ hh₂ -
        ordinaryGate d₁ h₁ hd₁ hh₁ * ordinaryGate d₂ h₂ hd₂ hh₂ =
      (((d₁ : ℤ) + h₁) * ((d₂ : ℤ) + h₂) - ((d₁ : ℤ) - h₁) * ((d₂ : ℤ) - h₂)) / 4 ∧
    (((d₁ : ℤ) + h₁) * ((d₂ : ℤ) + h₂) - ((d₁ : ℤ) - h₁) * ((d₂ : ℤ) - h₂)) / 4 =
      ((d₁ : ℤ) * h₂ + (h₁ : ℤ) * d₂) / 2 := by
  cases d₁ <;> cases h₁ <;> cases d₂ <;> cases h₂ <;>
    first
    | exact (hd₁ rfl).elim
    | exact (hh₁ rfl).elim
    | exact (hd₂ rfl).elim
    | exact (hh₂ rfl).elim
    | norm_num [ordinaryGate, rootGate, signTheta]

/-- eq:root-bowtie-recursion for every (G1) quadrilateral and root `g`, in the boundary
word `(a_0, a_1, a_2, a_3) = (P (g+1), P (g+2), P (g+3), P g)`:
`A_g = ((d₁+h₁)(d₂+h₂) - (d₁-h₁)(d₂-h₂))/4 = (d₁h₂ + h₁d₂)/2` with
`d₁ = χ(a_2,a_1,a_0)`, `d₂ = χ(a_3,a_2,a_1)`, `h₁ = χ(a_3,a_1,a_0)`, `h₂ = χ(a_3,a_2,a_0)`. -/
theorem quad_treeCoefficient (P : LabelledTuple 4) (hP : G1 P) (g : ZMod 4) :
    treeCoefficient P hP g (by norm_num) =
      (((chi P (g + 3) (g + 2) (g + 1) : ℤ) + chi P g (g + 2) (g + 1)) *
          ((chi P g (g + 3) (g + 2) : ℤ) + chi P g (g + 3) (g + 1)) -
        ((chi P (g + 3) (g + 2) (g + 1) : ℤ) - chi P g (g + 2) (g + 1)) *
          ((chi P g (g + 3) (g + 2) : ℤ) - chi P g (g + 3) (g + 1))) / 4 ∧
    treeCoefficient P hP g (by norm_num) =
      ((chi P (g + 3) (g + 2) (g + 1) : ℤ) * chi P g (g + 3) (g + 1) +
        (chi P g (g + 2) (g + 1) : ℤ) * chi P g (g + 3) (g + 2)) / 2 := by
  have h := smallValues_gate_formula _ _ _ _
    (quadTernaryComposition.nearSign_ne_zero hP g ⟨0, by decide⟩)
    (quadTernaryComposition.farSign_ne_zero hP g ⟨0, by decide⟩)
    (quadTernaryComposition.nearSign_ne_zero hP g ⟨1, by decide⟩)
    (quadTernaryComposition.farSign_ne_zero hP g ⟨1, by decide⟩)
  rw [quad_treeCoefficient_weights, quadTernaryComposition.smallValues_rootWeight_three P hP g rfl,
    quadTernaryComposition.smallValues_ordinaryWeight_three P hP g rfl, h.1]
  have h2 := h.2
  rw [quadTernaryComposition_nearSign_zero, quadTernaryComposition_farSign_zero,
    quadTernaryComposition_nearSign_one, quadTernaryComposition_farSign_one] at h2 ⊢
  exact ⟨rfl, h2⟩

omit [NeZero n] in
theorem smallValues_chi_pos {P : LabelledTuple n} {i j k : ZMod n}
    (h : 0 < det (P j - P i) (P k - P i)) : chi P i j k = 1 :=
  sign_eq_one_iff.mpr h

omit [NeZero n] in
theorem smallValues_chi_neg {P : LabelledTuple n} {i j k : ZMod n}
    (h : det (P j - P i) (P k - P i) < 0) : chi P i j k = -1 :=
  sign_eq_neg_one_iff.mpr h

/-- eq:root-bowtie-signs, the rows `g = 4 ≡ 0, 1, 2, 3` of the sign table
`(d₁, d₂, h₁, h₂)`, and `A_g(K_0) = -1` at each physical root. -/
theorem bowTie_treeCoefficient (g : ZMod 4) :
    treeCoefficient bowTie bowTie_G1 g (by norm_num) = -1 := by
  rw [(quad_treeCoefficient bowTie bowTie_G1 g).2]
  rcases (show g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 by decide +revert) with rfl | rfl | rfl | rfl
  · -- row g = 4: (d₁, d₂, h₁, h₂) = (-1, -1, 1, 1)
    have e1 : chi bowTie (0 + 3) (0 + 2) (0 + 1) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    have e2 : chi bowTie 0 (0 + 3) (0 + 2) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    have e3 : chi bowTie 0 (0 + 2) (0 + 1) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    have e4 : chi bowTie 0 (0 + 3) (0 + 1) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    rw [e1, e2, e3, e4]
    decide
  · -- row g = 1: (-1, 1, -1, 1)
    have e1 : chi bowTie (1 + 3) (1 + 2) (1 + 1) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    have e2 : chi bowTie 1 (1 + 3) (1 + 2) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    have e3 : chi bowTie 1 (1 + 2) (1 + 1) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    have e4 : chi bowTie 1 (1 + 3) (1 + 1) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    rw [e1, e2, e3, e4]
    decide
  · -- row g = 2: (1, 1, -1, -1)
    have e1 : chi bowTie (2 + 3) (2 + 2) (2 + 1) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    have e2 : chi bowTie 2 (2 + 3) (2 + 2) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    have e3 : chi bowTie 2 (2 + 2) (2 + 1) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    have e4 : chi bowTie 2 (2 + 3) (2 + 1) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    rw [e1, e2, e3, e4]
    decide
  · -- row g = 3: (1, -1, 1, -1)
    have e1 : chi bowTie (3 + 3) (3 + 2) (3 + 1) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    have e2 : chi bowTie 3 (3 + 3) (3 + 2) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    have e3 : chi bowTie 3 (3 + 2) (3 + 1) = 1 :=
      smallValues_chi_pos (by simp +decide [bowTie, det])
    have e4 : chi bowTie 3 (3 + 3) (3 + 1) = -1 :=
      smallValues_chi_neg (by simp +decide [bowTie, det])
    rw [e1, e2, e3, e4]
    decide

/-- lem:A-small-values (ii): `A_g(σ^k K_0) = -1` for every physical root `g` and every `k`
(cyclic shifts permute the root words, prop:A-reversal (i) = `treeCoefficient_shift`). -/
theorem A_small_values_ii (k g : ZMod 4) :
    treeCoefficient (shift k bowTie) (g1_shift_forward k bowTie_G1) g (by norm_num) = -1 := by
  have h := treeCoefficient_shift bowTie bowTie_G1 (g + k) k (by norm_num)
  rw [add_sub_cancel_right] at h
  rw [h]
  exact bowTie_treeCoefficient (g + k)

/-- `σ^k` for an integer `k` is `shift (k : ZMod 4)`; the same value. -/
theorem A_small_values_ii_int (k : ℤ) (g : ZMod 4) :
    treeCoefficient (shift (k : ZMod 4) bowTie) (g1_shift_forward (k : ZMod 4) bowTie_G1) g
      (by norm_num) = -1 :=
  A_small_values_ii _ g

omit [NeZero n] in
/-- The iterate `σ^k = (shift 1)^[k]` is `shift k`. -/
theorem smallValues_shift_iterate (k : ℕ) (P : LabelledTuple n) :
    (shift (1 : ZMod n))^[k] P = shift (k : ZMod n) P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, shift_add, Nat.cast_succ, add_comm]

end Quadrilateral

/-- lem:A-small-values, both clauses. -/
theorem A_small_values :
    (∀ (P : LabelledTuple 3) (hP : G1 P), ∃ τ : SignType, τ ≠ 0 ∧ (∀ i, turn P i = τ) ∧
      ∀ g, treeCoefficient P hP g (by norm_num) = -(τ : ℤ)) ∧
    (∀ k g : ZMod 4,
      treeCoefficient (shift k bowTie) (g1_shift_forward k bowTie_G1) g (by norm_num) = -1) :=
  ⟨A_small_values_i, A_small_values_ii⟩

end

end SM

