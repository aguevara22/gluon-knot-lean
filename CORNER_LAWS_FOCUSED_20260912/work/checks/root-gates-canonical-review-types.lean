import SM.Gates
import SM.FiniteCompositions

set_option pp.fullNames true
set_option pp.universes false
#check SM.boundaryIndex
#print axioms SM.boundaryIndex
#check SM.boundaryWord
#print axioms SM.boundaryWord
#check SM.boundaryIndex_injective
#print axioms SM.boundaryIndex_injective
#check SM.boundaryWord_shift
#print axioms SM.boundaryWord_shift
#check SM.boundaryWord_first
#print axioms SM.boundaryWord_first
#check SM.boundaryWord_last
#print axioms SM.boundaryWord_last
#check SM.boundaryWord_leaf_edge
#print axioms SM.boundaryWord_leaf_edge
#check SM.BoundaryInterval
#print axioms SM.BoundaryInterval
#check SM.BoundaryInterval.leaves
#print axioms SM.BoundaryInterval.leaves
#check SM.BoundaryInterval.leaves_pos
#print axioms SM.BoundaryInterval.leaves_pos
#check SM.IntervalComposition
#print axioms SM.IntervalComposition
#check SM.IntervalComposition.parts_lt
#print axioms SM.IntervalComposition.parts_lt
#check SM.IntervalComposition.part
#print axioms SM.IntervalComposition.part
#check SM.IntervalComposition.single
#print axioms SM.IntervalComposition.single
#check SM.rootData
#print axioms SM.rootData
#check SM.IntervalComposition.finiteCode
#print axioms SM.IntervalComposition.finiteCode
#check SM.IntervalComposition.finiteCode_injective
#print axioms SM.IntervalComposition.finiteCode_injective
#check SM.IntervalComposition.finite
#print axioms SM.IntervalComposition.finite
#check SM.IntervalComposition.fintype
#print axioms SM.IntervalComposition.fintype
#check SM.IntervalComposition.part_leaves_lt
#print axioms SM.IntervalComposition.part_leaves_lt
#check SM.signTheta
#print axioms SM.signTheta
#check SM.sign_product_nonzero
#print axioms SM.sign_product_nonzero
#check SM.ordinaryGate
#print axioms SM.ordinaryGate
#check SM.rootGate
#print axioms SM.rootGate
#check SM.gate_pair_identities
#print axioms SM.gate_pair_identities
#check SM.IntervalComposition.nearSign
#print axioms SM.IntervalComposition.nearSign
#check SM.IntervalComposition.farSign
#print axioms SM.IntervalComposition.farSign
#check SM.IntervalComposition.nearSign_ne_zero
#print axioms SM.IntervalComposition.nearSign_ne_zero
#check SM.IntervalComposition.farSign_ne_zero
#print axioms SM.IntervalComposition.farSign_ne_zero
#check SM.IntervalComposition.ordinaryWeight
#print axioms SM.IntervalComposition.ordinaryWeight
#check SM.IntervalComposition.rootWeight
#print axioms SM.IntervalComposition.rootWeight
#check SM.IntervalComposition.one_part_weights
#print axioms SM.IntervalComposition.one_part_weights
#check SM.IntervalComposition.binary_near_eq_far
#print axioms SM.IntervalComposition.binary_near_eq_far
#check SM.IntervalComposition.binary_ordinaryWeight_zero
#print axioms SM.IntervalComposition.binary_ordinaryWeight_zero
#check SM.gatesData
#print axioms SM.gatesData
#check SM.nonzero_sign_cases
#print axioms SM.nonzero_sign_cases
#check SM.gates_nonzero
#print axioms SM.gates_nonzero
#check SM.ordinaryGate_congr
#print axioms SM.ordinaryGate_congr
#check SM.rootGate_congr
#print axioms SM.rootGate_congr
#check SM.IntervalComposition.nearSign_shift
#print axioms SM.IntervalComposition.nearSign_shift
#check SM.IntervalComposition.farSign_shift
#print axioms SM.IntervalComposition.farSign_shift
#check SM.IntervalComposition.ordinaryWeight_eq_of_signs
#print axioms SM.IntervalComposition.ordinaryWeight_eq_of_signs
#check SM.IntervalComposition.rootWeight_eq_of_signs
#print axioms SM.IntervalComposition.rootWeight_eq_of_signs
#check SM.IntervalComposition.ordinaryWeight_shift
#print axioms SM.IntervalComposition.ordinaryWeight_shift
#check SM.IntervalComposition.rootWeight_shift
#print axioms SM.IntervalComposition.rootWeight_shift
#check SM.gatesData_shift
#print axioms SM.gatesData_shift
#print SM.rootData
#print SM.BoundaryInterval
#print SM.IntervalComposition
#print SM.signTheta
#print SM.IntervalComposition.nearSign
#print SM.IntervalComposition.farSign
#print SM.IntervalComposition.ordinaryWeight
#print SM.IntervalComposition.rootWeight
#print SM.gatesData

namespace RootBoundaryIndependentReview
open SM

-- Relabelling retains the same actual physical root vector and boundary word.
theorem simultaneous_root_shift {n : ℕ} [NeZero n]
    (P : LabelledTuple n) (g a : ZMod n) :
    edge (shift a P) (g - a) = edge P g ∧
      boundaryWord (shift a P) (g - a) = boundaryWord P g := by
  constructor
  · rw [edge_shift]
    simp
  · exact boundaryWord_shift P g a

-- Exactly the n-1 nonroot occurrence labels are traversed, including wraparound.
theorem leaf_index_exhaustion {n : ℕ} [NeZero n] (g : ZMod n) :
    (∀ k : Fin (n - 1), g + ((k.val + 1 : ℕ) : ZMod n) ≠ g) ∧
    ∀ e : ZMod n, e ≠ g → ∃ k : Fin (n - 1), g + ((k.val + 1 : ℕ) : ZMod n) = e := by
  have hn := NeZero.pos n
  constructor
  · intro k he
    have hz : ((k.val + 1 : ℕ) : ZMod n) = 0 := add_left_cancel (he.trans (add_zero g).symm)
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  · intro e he
    have hp : 0 < (e - g).val := Nat.pos_of_ne_zero (fun hz => he (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp hz)))
    have hlt := (e - g).val_lt
    let k : Fin (n - 1) := ⟨(e - g).val - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hk : k.val + 1 = (e - g).val := by dsimp [k]; omega
    rw [hk, ZMod.natCast_zmod_val]
    abel

-- The order positions are distinct actual labels; under G1 they are distinct
-- vertices. No G2 premise is used or supplied.
theorem boundary_vertices_distinct {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    Function.Injective (boundaryWord P g) :=
  (g1_vertices_injective hn hP).comp (boundaryIndex_injective g)

-- All cuts belong to the printed interval; each positive part is an interval.
theorem cut_containment {n : ℕ} (I : BoundaryInterval n) (π : IntervalComposition I) :
    (∀ k, I.left ≤ π.cut k ∧ π.cut k ≤ I.right) ∧
      ∀ k : Fin π.parts, 0 < (π.part k).leaves := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  refine ⟨?_, fun k => (π.part k).leaves_pos⟩
  intro k
  constructor
  · rw [← π.first]
    exact π.strict.monotone (Fin.zero_le k)
  · rw [← π.last]
    exact π.strict.monotone (Fin.le_last k)

-- The representation admits EVERY source natural strictly increasing list:
-- the Fin n cut bounds follow from its last cut, not from an extra hypothesis.
theorem raw_composition_admitted {n : ℕ} (I : BoundaryInterval n)
    (s : ℕ) (hs : 0 < s) (r : Fin (s + 1) → ℕ) (hr : StrictMono r)
    (hfirst : r 0 = I.left.val) (hlast : r (Fin.last s) = I.right.val) :
    let cuts : Fin (s + 1) → Fin n := fun k => ⟨r k,
      lt_of_le_of_lt (by rw [← hlast]; exact hr.monotone (Fin.le_last k)) I.right.isLt⟩
    ∃ π : IntervalComposition I, π.parts = s ∧ HEq π.cut cuts := by
  dsimp only
  let π : IntervalComposition I := {
    parts := s
    parts_pos := hs
    cut := fun k => ⟨r k, lt_of_le_of_lt (by rw [← hlast]; exact hr.monotone (Fin.le_last k)) I.right.isLt⟩
    strict := fun a b h => hr h
    first := Fin.ext hfirst
    last := Fin.ext hlast }
  exact ⟨π, rfl, HEq.rfl⟩

-- Finiteness of the ENTIRE arbitrary-natural-part-count type is derived by
-- embedding it into bounded part counts and finite functions, with no truncation.
theorem all_compositions_finite {n : ℕ} (I : BoundaryInterval n) :
    Finite (IntervalComposition I) := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  let f : IntervalComposition I → (Σ s : Fin n, Fin (s.val + 1) → Fin n) :=
    fun π => ⟨⟨π.parts, π.parts_lt⟩, π.cut⟩
  apply Finite.of_injective f
  rintro ⟨s, hs, c, hc, hc0, hc1⟩ ⟨t, ht, d, hd, hd0, hd1⟩ he
  have hst : s = t := congrArg (fun q => q.1.val) he
  subst t
  have hcd : c = d := eq_of_heq (Sigma.mk.inj he).2
  subst d
  rfl

-- A nonempty one-part composition exists for every valid source interval.
theorem one_part_exists {n : ℕ} (I : BoundaryInterval n) :
    ∃ π : IntervalComposition I, π.parts = 1 ∧ π.part ⟨0, π.parts_pos⟩ = I := by
  refine ⟨IntervalComposition.single I, rfl, ?_⟩
  cases I
  rfl

-- The root denotes the actual placed segment and both placed endpoints,
-- not only an edge vector shared by possibly different geometric edges.
theorem root_segment_and_endpoints_shift {n : ℕ} [NeZero n]
    (P : LabelledTuple n) (g a : ZMod n) :
    edgeSegment (shift a P) (g - a) = edgeSegment P g ∧
      (shift a P) (g - a) = P g ∧
      (shift a P) (g - a + 1) = P (g + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeSegment_shift]
    simp
  · simp [shift]
  · change P (g - a + 1 + a) = P (g + 1)
    congr 1
    ring

end RootBoundaryIndependentReview

#print axioms RootBoundaryIndependentReview.simultaneous_root_shift
#print axioms RootBoundaryIndependentReview.leaf_index_exhaustion
#print axioms RootBoundaryIndependentReview.boundary_vertices_distinct
#print axioms RootBoundaryIndependentReview.cut_containment
#print axioms RootBoundaryIndependentReview.raw_composition_admitted
#print axioms RootBoundaryIndependentReview.all_compositions_finite
#print axioms RootBoundaryIndependentReview.one_part_exists
#print axioms RootBoundaryIndependentReview.root_segment_and_endpoints_shift

namespace FiniteAndGatesIndependentReview
open SM

-- The canonical typeclass domain is the unchanged source composition type.
theorem every_composition_enumerated {n : ℕ} [NeZero n] (I : BoundaryInterval n) :
    (∀ π : IntervalComposition I, π ∈ (Finset.univ : Finset (IntervalComposition I))) ∧
      0 < Fintype.card (IntervalComposition I) := by
  exact ⟨fun _ => Finset.mem_univ _, Fintype.card_pos_iff.mpr ⟨IntervalComposition.single I⟩⟩

-- Actual child intervals have positive and strictly smaller leaf counts.
theorem all_source_children_decrease {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (hp : 2 ≤ π.parts) :
    ∀ k : Fin π.parts, 0 < (π.part k).leaves ∧ (π.part k).leaves < I.leaves :=
  fun k => ⟨(π.part k).leaves_pos, π.part_leaves_lt hp k⟩

-- The exact source recursive-child relation is well founded under that measure.
theorem source_child_relation_wellFounded {n : ℕ} [NeZero n] :
    WellFounded (fun J I : BoundaryInterval n =>
      ∃ π : IntervalComposition I, 2 ≤ π.parts ∧ ∃ k : Fin π.parts, J = π.part k) := by
  apply (measure BoundaryInterval.leaves).wf.mono
  intro J I h
  obtain ⟨π, hp, k, rfl⟩ := h
  exact π.part_leaves_lt hp k

-- The excluded one-part case has equal measure, not a false strict decrease.
theorem singleton_measure_equal {n : ℕ} [NeZero n] (I : BoundaryInterval n) :
    ((IntervalComposition.single I).part ⟨0, (IntervalComposition.single I).parts_pos⟩).leaves = I.leaves := by
  cases I
  rfl

-- Every source interior cut1<=k<=s-1 has exactly an indexing position k-1.
theorem interior_cut_exhaustion {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (k : ℕ) (hk : 0 < k) (hks : k < π.parts) :
    ∃ j : Fin (π.parts - 1), j.val + 1 = k := by
  exact ⟨⟨k - 1, by omega⟩, by simp; omega⟩

-- The nonzero SignType step is the source Real step on every actual gate argument.
theorem real_step_interpretation (s : SignType) (hs : s ≠ 0) :
    (signTheta s hs : ℝ) = (if 0 < (s : ℝ) then 1 else 0) := by
  cases s <;> first | exact (hs rfl).elim | norm_num [signTheta]

-- Both half-formulas are exact rational/real identities, not rounded integer division.
theorem real_gate_identities (d h : SignType) (hd : d ≠ 0) (hh : h ≠ 0) :
    (ordinaryGate d h hd hh : ℝ) = ((d : ℝ) - (h : ℝ)) / 2 ∧
    (rootGate d h hd hh : ℝ) = ((d : ℝ) + (h : ℝ)) / 2 := by
  cases d <;> cases h <;>
    first | exact (hd rfl).elim | exact (hh rfl).elim |
      norm_num [ordinaryGate, rootGate, signTheta]

-- Embedding the actual complete weights gives the product of the source halves.
theorem real_weight_identities {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.ordinaryWeight P hP g : ℝ) = ∏ k : Fin (π.parts - 1),
      ((π.nearSign P g k : ℝ) - (π.farSign P g k : ℝ)) / 2 ∧
    (π.rootWeight P hP g : ℝ) = ∏ k : Fin (π.parts - 1),
      ((π.nearSign P g k : ℝ) + (π.farSign P g k : ℝ)) / 2 := by
  constructor
  · rw [IntervalComposition.ordinaryWeight, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact (real_gate_identities _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).1
  · rw [IntervalComposition.rootWeight, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact (real_gate_identities _ _ (π.nearSign_ne_zero hP g k) (π.farSign_ne_zero hP g k)).2

-- Empty products and the arbitrary two-part source composition need only G1.
theorem source_small_part_cases {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    (π.parts = 1 → π.ordinaryWeight P hP g = 1 ∧ π.rootWeight P hP g = 1) ∧
    (π.parts = 2 → π.ordinaryWeight P hP g = 0) :=
  ⟨π.one_part_weights P hP g, π.binary_ordinaryWeight_zero P hP g⟩

-- Independent check of the representative-equivalence obligation.
theorem gate_signs_shift {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (g a : ZMod n)
    (k : Fin (π.parts - 1)) :
    π.nearSign (shift a P) (g - a) k = π.nearSign P g k ∧
      π.farSign (shift a P) (g - a) k = π.farSign P g k := by
  have hb : ∀ j : Fin n, boundaryIndex (g - a) j + a = boundaryIndex g j := by
    intro j
    unfold boundaryIndex
    ring
  constructor
  · simp only [IntervalComposition.nearSign, chi_shift, hb]
  · simp only [IntervalComposition.farSign, chi_shift, hb]

-- All factors and weights preserve the pair(polygon,root), including G1 transport.
theorem gate_weights_shift {n : ℕ} [NeZero n] (I : BoundaryInterval n)
    (π : IntervalComposition I) (P : LabelledTuple n) (hP : G1 P) (g a : ZMod n) :
    π.ordinaryWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.ordinaryWeight P hP g ∧
    π.rootWeight (shift a P) (g1_shift_forward a hP) (g - a) = π.rootWeight P hP g := by
  constructor
  · unfold IntervalComposition.ordinaryWeight
    apply Finset.prod_congr rfl
    intro k _
    rcases gate_signs_shift I π P g a k with ⟨hd, hh⟩
    simp only [hd, hh]
  · unfold IntervalComposition.rootWeight
    apply Finset.prod_congr rfl
    intro k _
    rcases gate_signs_shift I π P g a k with ⟨hd, hh⟩
    simp only [hd, hh]

end FiniteAndGatesIndependentReview

#print axioms FiniteAndGatesIndependentReview.every_composition_enumerated
#print axioms FiniteAndGatesIndependentReview.all_source_children_decrease
#print axioms FiniteAndGatesIndependentReview.source_child_relation_wellFounded
#print axioms FiniteAndGatesIndependentReview.singleton_measure_equal
#print axioms FiniteAndGatesIndependentReview.interior_cut_exhaustion
#print axioms FiniteAndGatesIndependentReview.real_step_interpretation
#print axioms FiniteAndGatesIndependentReview.real_gate_identities
#print axioms FiniteAndGatesIndependentReview.real_weight_identities
#print axioms FiniteAndGatesIndependentReview.source_small_part_cases
#print axioms FiniteAndGatesIndependentReview.gate_signs_shift
#print axioms FiniteAndGatesIndependentReview.gate_weights_shift

namespace GatesEquivarianceIndependentReview
open SM

-- The source generator sigma sends the root g exactly to g-1.
theorem source_generator {n : ℕ} [NeZero n] (P : LabelledTuple n) (hP : G1 P) (g : ZMod n) :
    gatesData (shift 1 P) (g1_shift_forward 1 hP) (g - 1) = gatesData P hP g :=
  gatesData_shift P hP g 1

-- Any two allowed representative/root presentations give the same whole data.
-- A different proof of G1 for the shifted representative cannot change it.
theorem rooted_representative_descent {n : ℕ} [NeZero n]
    (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q) (g h a : ZMod n)
    (hQeq : Q = shift a P) (hroot : h = g - a) :
    gatesData Q hQ h = gatesData P hP g := by
  subst Q
  subst h
  exact gatesData_shift P hP g a

-- The proof-carrying nonzero interface carries no numerical proof dependence.
theorem G1_proof_independence {n : ℕ} [NeZero n] (P : LabelledTuple n)
    (hP hP' : G1 P) (g : ZMod n) : gatesData P hP g = gatesData P hP' g := rfl

end GatesEquivarianceIndependentReview

#print axioms GatesEquivarianceIndependentReview.source_generator
#print axioms GatesEquivarianceIndependentReview.rooted_representative_descent
#print axioms GatesEquivarianceIndependentReview.G1_proof_independence
