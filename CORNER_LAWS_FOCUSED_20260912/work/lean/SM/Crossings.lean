import SM.CrossingCriterion
import Mathlib.Data.Finset.Powerset

/-! Actual unordered crossings, their unique points and parameters.
Unordered pairs are represented by two-element Finsets, with distinctness
forced by remoteness; there is no ordering or chosen root in a crossing. -/

namespace SM

variable {n : ℕ}

def IsCrossing (P : LabelledTuple n) (s : Finset (ZMod n)) : Prop :=
  ∃ i j, s = {i, j} ∧ remote i j ∧ (edgeSegment P i ∩ edgeSegment P j).Nonempty

def Crossing (P : LabelledTuple n) := {s : Finset (ZMod n) // IsCrossing P s}

noncomputable def crossingSet [NeZero n] (P : LabelledTuple n) : Finset (Finset (ZMod n)) := by
  classical
  exact Finset.univ.powerset.filter (IsCrossing P)

theorem mem_crossingSet [NeZero n] (P : LabelledTuple n) (s : Finset (ZMod n)) :
    s ∈ crossingSet P ↔ IsCrossing P s := by
  simp [crossingSet]

theorem crossing_card_two {P : LabelledTuple n} (c : Crossing P) : c.val.card = 2 := by
  obtain ⟨i, j, hs, hr, _⟩ := c.property
  rw [hs]
  exact Finset.card_pair (remote_endpoints i j hr).1.symm

theorem crossing_common_point_exists {P : LabelledTuple n} (c : Crossing P) :
    ∃ x : Plane, ∀ i ∈ c.val, x ∈ edgeSegment P i := by
  obtain ⟨i, j, hs, _, x, hxi, hxj⟩ := c.property
  refine ⟨x, ?_⟩
  intro k hk
  rw [hs] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact hxi
  · exact hxj

noncomputable def crossingPoint {P : LabelledTuple n} (c : Crossing P) : Plane :=
  Classical.choose (crossing_common_point_exists c)

theorem crossingPoint_mem {P : LabelledTuple n} (c : Crossing P) (i : ZMod n)
    (hi : i ∈ c.val) : crossingPoint c ∈ edgeSegment P i :=
  Classical.choose_spec (crossing_common_point_exists c) i hi

theorem crossingPoint_interior [Nontrivial (ZMod n)]
    {P : LabelledTuple n} (h : G1 P) (c : Crossing P) (k : ZMod n) (hk : k ∈ c.val) :
    crossingPoint c ∈ edgeInterior P k := by
  obtain ⟨i, j, hs, hr, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  have hm := g1_remote_meeting h hr (crossingPoint_mem c i hi) (crossingPoint_mem c j hj)
  rw [hs] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact hm.1
  · exact hm.2.1

theorem crossingPoint_unique [Nontrivial (ZMod n)]
    {P : LabelledTuple n} (h : G1 P) (c : Crossing P) (x : Plane)
    (hx : ∀ i ∈ c.val, x ∈ edgeSegment P i) : x = crossingPoint c := by
  obtain ⟨i, j, hs, hr, _⟩ := c.property
  have hi : i ∈ c.val := by rw [hs]; simp
  have hj : j ∈ c.val := by rw [hs]; simp
  exact (g1_remote_meeting h hr (crossingPoint_mem c i hi)
    (crossingPoint_mem c j hj)).2.2.2 x (hx i hi) (hx j hj)

noncomputable def crossingParameter {P : LabelledTuple n} (c : Crossing P)
    (i : ZMod n) (hi : i ∈ c.val) : ℝ :=
  Classical.choose (crossingPoint_mem c i hi)

theorem crossingParameter_spec {P : LabelledTuple n} (c : Crossing P)
    (i : ZMod n) (hi : i ∈ c.val) :
    0 ≤ crossingParameter c i hi ∧ crossingParameter c i hi ≤ 1 ∧
    crossingPoint c = edgePoint P i (crossingParameter c i hi) :=
  Classical.choose_spec (crossingPoint_mem c i hi)

noncomputable def crossingSign (P : LabelledTuple n) (i j : ZMod n) : SignType :=
  SignType.sign (det (edge P i) (edge P j))

theorem crossingSign_swap (P : LabelledTuple n) (i j : ZMod n) :
    crossingSign P j i = -crossingSign P i j := by
  unfold crossingSign
  rw [det_swap, Left.sign_neg]

theorem edgePoint_injective {P : LabelledTuple n} {i : ZMod n}
    (h : edge P i ≠ 0) : Function.Injective (edgePoint P i) := by
  intro s t he
  have he' : s • edge P i = t • edge P i := add_left_cancel he
  by_contra hst
  have hz : (s - t) • edge P i = 0 := by rw [sub_smul, he', sub_self]
  have hx := congrArg Prod.fst hz
  have hy := congrArg Prod.snd hz
  change (s - t) * (edge P i).1 = 0 at hx
  change (s - t) * (edge P i).2 = 0 at hy
  apply h
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hst))
    ((mul_eq_zero.mp hy).resolve_left (sub_ne_zero.mpr hst))

theorem crossingParameter_interior (hn : 3 ≤ n) {P : LabelledTuple n} (h : G1 P)
    (c : Crossing P) (i : ZMod n) (hi : i ∈ c.val) :
    0 < crossingParameter c i hi ∧ crossingParameter c i hi < 1 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨t, ht0, ht1, ht⟩ := crossingPoint_interior h c i hi
  have he := (crossingParameter_spec c i hi).2.2.symm.trans ht
  have hp := edgePoint_injective (g1_edge_ne_zero hn h i) he
  rw [hp]
  exact ⟨ht0, ht1⟩

theorem generic_crossingPoint_injective (hn : 3 ≤ n) {P : LabelledTuple n}
    (h : Generic P) : Function.Injective (@crossingPoint n P) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro c d hpoint
  have support_subset (c d : Crossing P) (heq : crossingPoint c = crossingPoint d) :
      c.val ⊆ d.val := by
    obtain ⟨i, j, hs, hr, _⟩ := d.property
    have hi : i ∈ d.val := by rw [hs]; simp
    have hj : j ∈ d.val := by rw [hs]; simp
    intro k hk
    by_contra hnot
    have hki : k ≠ i := by intro he; subst k; exact hnot hi
    have hkj : k ≠ j := by intro he; subst k; exact hnot hj
    have hxk := crossingPoint_interior h.1 c k hk
    rw [heq] at hxk
    apply h.2
    exact ⟨i, j, k, crossingPoint d, (remote_endpoints i j hr).1.symm,
      hkj.symm, hki.symm, crossingPoint_interior h.1 d i hi,
      crossingPoint_interior h.1 d j hj, hxk⟩
  apply Subtype.ext
  exact Finset.Subset.antisymm (support_subset c d hpoint) (support_subset d c hpoint.symm)

theorem crossing_set_finite [NeZero n] (P : LabelledTuple n) :
    Set.Finite {s : Finset (ZMod n) | IsCrossing P s} := by
  have heq : {s : Finset (ZMod n) | IsCrossing P s} = (crossingSet P : Set _) := by
    ext s
    exact (mem_crossingSet P s).symm
  rw [heq]
  exact Finset.finite_toSet _

theorem isCrossing_pair (P : LabelledTuple n) (i j : ZMod n) (hr : remote i j) :
    IsCrossing P {i, j} ↔ (edgeSegment P i ∩ edgeSegment P j).Nonempty := by
  constructor
  · intro h
    let c : Crossing P := ⟨{i, j}, h⟩
    exact ⟨crossingPoint c, crossingPoint_mem c i (by simp [c]),
      crossingPoint_mem c j (by simp [c])⟩
  · intro h
    exact ⟨i, j, rfl, hr, h⟩

/-- All three conclusions of the source crossing-test lemma, using the actual
unordered-crossing predicate. -/
theorem crossing_test (hn : 3 ≤ n) (P : LabelledTuple n) (h : G1 P) :
    (∀ i j, remote i j →
      (IsCrossing P {i, j} ↔
        chi P i (i + 1) j * chi P i (i + 1) (j + 1) = -1 ∧
        chi P j (j + 1) i * chi P j (j + 1) (i + 1) = -1)) ∧
    (Generic P → Function.Injective (@crossingPoint n P)) ∧
    Set.Finite {s : Finset (ZMod n) | IsCrossing P s} := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨?_, fun hg => generic_crossingPoint_injective hn hg, crossing_set_finite P⟩
  intro i j hr
  exact (isCrossing_pair P i j hr).trans (crossing_test_iff hn P h i j hr)

end SM
