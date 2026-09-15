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
